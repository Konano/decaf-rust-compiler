use crate::{TypeCk, TypeCkTrait};
use common::{ErrorKind::*, Loc, LENGTH, BinOp, UnOp, ErrorKind, Ref};
use syntax::ast::*;
use syntax::{ScopeOwner, Symbol, ty::*};
use std::{ops::{Deref, DerefMut}, iter};

pub(crate) struct TypePass<'a>(pub TypeCk<'a>);

impl<'a> Deref for TypePass<'a> {
  type Target = TypeCk<'a>;
  fn deref(&self) -> &Self::Target { &self.0 }
}

impl<'a> DerefMut for TypePass<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl<'a> TypePass<'a> {
  pub fn program(&mut self, p: &'a Program<'a>) {
    for c in &p.class { self.class_def(c); }
  }

  fn class_def(&mut self, c: &'a ClassDef<'a>) {
    self.cur_class = Some(c); 
    self.scoped(ScopeOwner::Class(c), |s| for f in &c.field {
      if let FieldDef::FuncDef(f) = f {
        s.cur_func = Some(f);
        if f.body.is_none() == false {
          let ret = s.scoped(ScopeOwner::Param(f), |s| s.block(&f.body.as_ref().unwrap(), false));
          if ret.1.kind == TyKind::Void && f.ret_ty() != Ty::void() {
            s.issue(f.body.as_ref().unwrap().loc, ErrorKind::NoReturn)
          }
        }
      };
    });
  }

  fn block(&mut self, b: &'a Block<'a>, rt: bool) -> (bool, Ty<'a>) {
    let mut ret = (false, Ty::void());
    self.scoped(ScopeOwner::Local(b), |s| for st in &b.stmt { 
      let stmt_ret = s.stmt(st);
      ret = s.combine(ret, stmt_ret, false);
    });
    if rt && ret.0 == false && ret.1.kind != TyKind::Void { self.issue(b.loc, MissingReturnStatement) }
    if rt && ret.1.kind == TyKind::Error { self.issue(b.loc, IncompatibleTypes) }
    ret
  }

  // return whether this stmt has a return value
  fn stmt(&mut self, s: &'a Stmt<'a>) -> (bool, Ty<'a>) {
    match &s.kind {
      StmtKind::Assign(a) => {
        self.cur_assign = Some(s.loc);
        let l = self.expr(&a.dst);
        let r = self.expr(&a.src);
        self.cur_assign = None;
        if !r.assignable_to(l) { 
          self.issue(s.loc, IncompatibleBinary { l, op: "=", r }) 
        } else if l.is_func() {
          if let ExprKind::VarSel(v) = &a.dst.kind {
            self.issue(s.loc, AssignToMethod(v.name))
          }
        }
        (false, Ty::void())
      }
      StmtKind::LocalVarDef(v) => {
        self.cur_var_def = Some(v);
        self.cur_def.push(v.loc);
        if let Some((loc, e)) = &v.init {
          let l = v.ty.get();
          self.cur_assign = Some(s.loc);
          let r = self.expr(e);
          self.cur_assign = None;
          if l.kind == TyKind::Var { 
            if r.kind == TyKind::Void {
              self.issue(v.loc, VoidVar(v.name))
            } else { v.ty.set(r) }
          } else if !r.assignable_to(l) { 
            self.issue(*loc, IncompatibleBinary { l, op: "=", r }) 
          } else {
            match r.kind { 
              TyKind::Object(Ref(c)) => if c.abstract_ {
                self.issue(e.loc, NewAbstractClass(c.name)) 
              }, 
              _ => {}, 
            };
          }
        }
        self.cur_var_def = None;
        self.cur_def.pop();
        (false, Ty::void())
      }
      StmtKind::ExprEval(e) => {
        self.expr(e);
        (false, Ty::void())
      }
      StmtKind::Skip(_) => (false, Ty::void()),
      StmtKind::If(i) => {
        self.check_bool(&i.cond);
        let mut l = self.block(&i.on_true, false);
        let mut r = i.on_false.as_ref().map(|b| self.block(b, false)).unwrap_or((false, Ty::void()));
        l.0 = l.0 && r.0; r.0 = l.0;
        self.combine(l, r, false)
      }
      StmtKind::While(w) => {
        self.check_bool(&w.cond);
        self.loop_cnt += 1;
        let ret = self.block(&w.body, false);
        self.loop_cnt -= 1;
        ret
      }
      StmtKind::For(f) => self.scoped(ScopeOwner::Local(&f.body), |s| {
        s.stmt(&f.init);
        s.check_bool(&f.cond);
        s.stmt(&f.update);
        let mut ret = (false, Ty::void());
        for st in &f.body.stmt { 
          let stmt_ret = s.stmt(st);
          ret = s.combine(ret, stmt_ret, false);
        }
        // not calling block(), because the scope is already opened
        ret.0 = false;
        ret
      }),
      StmtKind::Return(r) => {
        let expect = if self.in_func() {
          self.cur_func.unwrap().ret_ty()
        } else { Ty::var() };
        let actual = r.as_ref().map(|e| self.expr(e)).unwrap_or(Ty::void());
        if !actual.assignable_to(expect) { self.issue(s.loc, ReturnMismatch { actual, expect }) }
        (true, actual)
      }
      StmtKind::Print(p) => {
        for (i, e) in p.iter().enumerate() {
          let ty = self.expr(e);
          if ty != Ty::bool() && ty != Ty::int() && ty != Ty::string() {
            ty.error_or(|| self.issue(e.loc, BadPrintArg { loc: i as u32 + 1, ty }))
          }
        }
        (false, Ty::void())
      }
      StmtKind::Break(_) => {
        if self.loop_cnt == 0 { self.issue(s.loc, BreakOutOfLoop) }
        (false, Ty::void())
      }
      StmtKind::Block(b) => self.block(b, false),
    }
  }

  // e.ty is set to the return value
  fn expr(&mut self, e: &'a Expr<'a>) -> Ty<'a> {
    use ExprKind::*;
    let ty = match &e.kind {
      VarSel(v) => self.var_sel(v, e.loc),
      IndexSel(i) => {
        self.cur_idx = true;
        let (arr, idx) = (self.expr(&i.arr), self.expr(&i.idx));
        self.cur_idx = false;
        if idx != Ty::int() { idx.error_or(|| self.issue(e.loc, IndexNotInt)) }
        match arr {
          Ty { arr, kind } if arr > 0 => Ty { arr: arr - 1, kind },
          e => e.error_or(|| self.issue(i.arr.loc, IndexNotArray)),
        }
      }
      IntLit(_) | ReadInt(_) => Ty::int(), BoolLit(_) => Ty::bool(), StringLit(_) | ReadLine(_) => Ty::string(), NullLit(_) => Ty::null(),
      Call(c) => self.call(c, e.loc),
      Unary(u) => {
        let r = self.expr(&u.r);
        let (ty, op) = match u.op { UnOp::Neg => (Ty::int(), "-"), UnOp::Not => (Ty::bool(), "!"), };
        if r != ty { r.error_or(|| self.issue(e.loc, IncompatibleUnary { op, r })) }
        ty
      }
      Binary(b) => {
        use BinOp::*;
        let (l, r) = (self.expr(&b.l), self.expr(&b.r));
        if l.kind == TyKind::Error || r.kind == TyKind::Error {
          // not using wildcard match, so that if we add new operators in the future, compiler can tell us
          match b.op { Add | Sub | Mul | Div | Mod => Ty::int(), And | Or | Eq | Ne | Lt | Le | Gt | Ge => Ty::bool() }
        } else {
          let (ret, ok) = match b.op {
            Add | Sub | Mul | Div | Mod => (Ty::int(), l == Ty::int() && r == Ty::int()),
            Lt | Le | Gt | Ge => (Ty::bool(), l == Ty::int() && r == Ty::int()),
            Eq | Ne => (Ty::bool(), l.assignable_to(r) || r.assignable_to(l)),
            And | Or => (Ty::bool(), l == Ty::bool() && r == Ty::bool())
          };
          if !ok { 
            self.issue(e.loc, IncompatibleBinary { l, op: b.op.to_op_str(), r }) 
          }
          ret
        }
      }
      This(_) => {
        if self.cur_func.unwrap().static_ { self.issue(e.loc, ThisInStatic) }
        Ty::mk_obj(self.cur_class.unwrap())
      }
      NewClass(n) => if let Some(c) = self.scopes.lookup_class(n.name) {
        n.class.set(Some(c));
        Ty::mk_obj(c)
      } else { self.issue(e.loc, NoSuchClass(n.name)) },
      NewArray(n) => {
        let len = self.expr(&n.len);
        if len != Ty::int() { len.error_or(|| self.issue(n.len.loc, NewArrayNotInt)) }
        self.ty(&n.elem, true)
      }
      ClassTest(c) => {
        let src = self.expr(&c.expr);
        if !src.is_object() { src.error_or(|| self.issue(e.loc, NotObject(src))) }
        if let Some(cl) = self.scopes.lookup_class(c.name) {
          c.class.set(Some(cl));
          Ty::bool()
        } else { self.issue(e.loc, NoSuchClass(c.name)) }
      }
      ClassCast(c) => {
        let src = self.expr(&c.expr);
        if !src.is_object() { src.error_or(|| self.issue(e.loc, NotObject(src))) }
        if let Some(cl) = self.scopes.lookup_class(c.name) {
          c.class.set(Some(cl));
          Ty::mk_obj(cl)
        } else { self.issue(e.loc, NoSuchClass(c.name)) }
      }
      Lambda(f) => self.lambda(f),
    };
    e.ty.set(ty);
    ty
  }

  fn var_sel(&mut self, v: &'a VarSel<'a>, loc: Loc) -> Ty<'a> {
    // (no owner)not_found_var / ClassName(no field) / (no owner)method => UndeclaredVar
    // object.not_found_var => NoSuchField
    // (no owner)field_var && cur function is static => RefInStatic
    // <not object>.a (e.g.: Class.a, 1.a) / object.method => BadFieldAccess
    // object.field_var, where object's class is not self or any of ancestors => PrivateFieldAccess

    if let Some(owner) = &v.owner {
      self.cur_used = true;
      let owner = self.expr(owner);
      self.cur_used = false;
      match owner {
        Ty { arr: 0, kind: TyKind::Object(Ref(c)) } => if let Some(sym) = c.lookup(v.name) {
          match sym {
            Symbol::Var(var) => {
              v.var.set(Some(var));
              // only allow self & descendents to access field
              if !self.cur_class.unwrap().extends(c) {
                self.issue(loc, PrivateFieldAccess { name: v.name, owner })
              }
              var.ty.get()
            }
            Symbol::Class(c) => Ty::mk_class(c),
            Symbol::Func(f) => Ty::mk_func(f),
            _ => self.issue(loc, BadFieldAccess { name: v.name, owner }),
          }
        } else { self.issue(loc, NoSuchField { name: v.name, owner }) },
        Ty { arr: 0, kind: TyKind::Class(Ref(c)) } => if let Some(sym) = c.lookup(v.name) {
          match sym {
            Symbol::Class(c) => Ty::mk_class(c),
            Symbol::Func(f) => {
              if f.static_ { Ty::mk_func(f) } else { self.issue(loc, BadFieldAccess { name: v.name, owner }) }
            }
            _ => self.issue(loc, BadFieldAccess { name: v.name, owner }),
          }
        } else { self.issue(loc, NoSuchField { name: v.name, owner }) },
        e => {
          if v.name == LENGTH && owner.is_arr() {
            Ty::new(TyKind::Lambda(self.alloc.ty.alloc_extend(vec![Ty::int()])))
          } else {
            e.error_or(|| self.issue(loc, BadFieldAccess { name: v.name, owner }))
          }
        },
      }
    } else {
      // if this stmt is in an VarDef, it cannot access the variable that is being declared
      if let Some(sym) = self.scopes.lookup_before(v.name, self.cur_var_def.map(|v| v.loc).unwrap_or(loc)) {
        match sym {
          Symbol::Var(var) => {
            if self.is_lvalue(loc) && 
               self.in_lambda() && 
               !self.cur_used && 
               !self.cur_idx &&
               self.cur_func.unwrap().loc < var.loc && 
               var.loc < self.cur_lambda.unwrap().loc
            {
              let _loc = self.cur_assign.unwrap();
              self.issue(_loc, AssignErrorInLambda)
            }
            if self.is_rvalue(loc) && self.cur_def.iter().any(|_loc| *_loc == var.loc) {
              self.issue(loc, UndeclaredVar(v.name))
            } else {
              v.var.set(Some(var));
              if var.owner.get().unwrap().is_class() {
                let cur = self.cur_func.unwrap();
                if cur.static_ {
                  self.issue(loc, RefInStatic { field: v.name, func: cur.name })
                }
              }
              var.ty.get()
            }
          }
          Symbol::Class(c) if self.cur_used => { Ty::mk_class(c) }
          Symbol::Func(c) => {
            let cur = self.cur_func.unwrap();
            if cur.static_ && !c.static_ {
              self.issue(loc, RefInStatic { field: v.name, func: cur.name })
            }
            Ty::mk_func(c)
          }
          _ => self.issue(loc, UndeclaredVar(v.name)),
        }
      } else { self.issue(loc, UndeclaredVar(v.name)) }
    }
  }

  fn lambda(&mut self, f: &'a Lambda<'a>) -> Ty<'a> {
    let _cur_lambda = self.cur_lambda;
    self.cur_lambda = Some(f);
    self.scoped(ScopeOwner::Lambda(f), |s| {
      let ret_ty = if f.body.is_left() {
        (true, s.expr(f.body.as_ref().left().unwrap()))
      } else { 
        s.block(f.body.as_ref().right().unwrap(), true)
      };
      let ret_param_ty = iter::once(ret_ty.1).chain(f.param.iter().map(|v| v.ty.get()));
      let ret_param_ty = s.alloc.ty.alloc_extend(ret_param_ty);
      f.ret_param_ty.set(Some(ret_param_ty));
    });
    self.cur_lambda = _cur_lambda;
    Ty::mk_lambda(f)
  }

  fn call(&mut self, c: &'a Call<'a>, loc: Loc) -> Ty<'a> {
    use ExprKind::*;
    match &c.func.kind {
      VarSel(v) => {
        let owner = if let Some(owner) = &v.owner {
          self.cur_used = true;
          let owner = self.expr(owner);
          self.cur_used = false;
          if owner.kind == TyKind::Error { return owner; }
          if v.name == LENGTH && owner.is_arr() {
            if !c.arg.is_empty() {
              self.issue(loc, LengthWithArgument(c.arg.len() as u32))
            }
            return Ty::int();
          }
          owner
        } else if let Some(sym) = self.scopes.lookup_before(v.name, self.cur_var_def.map(|v| v.loc).unwrap_or(loc)) {
          match sym {
            Symbol::Var(var) => {
              // v.var.set(Some(var));
              // if var.owner.get().unwrap().is_class() {
              //   unimplemented!()
              //   // let cur = self.cur_func.unwrap();
              //   // if cur.static_ {
              //   //   self.issue(loc, RefInStatic { field: v.name, func: cur.name })
              //   // }
              // }
              return match var.ty.get().kind {
                TyKind::Lambda(_v) | TyKind::Func(_v) => self.check_arg_param(&c.arg, _v, v.name, loc),
                TyKind::Var | TyKind::Error => Ty::error(),
                _ => self.issue(loc, NotCallable(var.ty.get()))
              }
              // return if let TyKind::Func(v) = var.ty.get().kind {
                // self.check_lambda_arg_param(&c.arg, v, loc)
                // let ret = if v.len() - 1 != c.arg.len() {
                  // for idx in 1..(v.len()-1) {
                  //   if !v.get(idx).is_none() {
                  //     if v.get(idx).unwrap(){
                        
                  //     }
                  //   }
                  // }
                  
                  // self.issue(loc, LambdaArgcMismatch { expect: (v.len() - 1) as u32, actual: c.arg.len() as u32 })
                // } else { v[0] };
                // ret
              // } else {
              // }
            },
            Symbol::Func(_) => Ty::mk_obj(self.cur_class.unwrap()),
            _ => Ty::error(), // Impossible
          }
        } else { Ty::error() };
        match owner {
          Ty { arr: 0, kind: TyKind::Object(Ref(cl)) } | Ty { arr: 0, kind: TyKind::Class(Ref(cl)) } => {
            if let Some(sym) = cl.lookup(v.name) {
              match sym {
                Symbol::Func(f) => {
                  c.func_ref.set(Some(f));
                  if owner.is_class() && !f.static_ {
                    // Class.not_static_method()
                    self.issue(c.func.loc, BadFieldAccess { name: v.name, owner })
                  }
                  if v.owner.is_none() {
                    let cur = self.cur_func.unwrap();
                    if cur.static_ && !f.static_ {
                      self.issue(c.func.loc, RefInStatic { field: f.name, func: cur.name })
                    }
                  }
                  self.check_arg_param(&c.arg, f.ret_param_ty.get().unwrap(), f.name, loc)
                }
                Symbol::Var(v) => {
                  match v.ty.get().kind {
                    TyKind::Lambda(_v) => self.check_lambda_arg_param(&c.arg, _v, loc),
                    TyKind::Var | TyKind::Error => Ty::error(),
                    _ => self.issue(loc, NotCallable(v.ty.get())),
                  }
                }
                _ => self.issue(loc, NotFunc { name: v.name, owner }),
              }
            } else { self.issue(c.func.loc, NoSuchField { name: v.name, owner }) }
          }
          _ => {
            if owner.kind == TyKind::Error {
              self.issue(c.func.loc, UndeclaredVar(v.name))
            } else {
              self.issue(c.func.loc, BadFieldAccess { name: v.name, owner })
            }
          }
        }
      }
      Lambda(f) => {
        self.lambda(f);
        self.check_lambda_arg_param(&c.arg, f.ret_param_ty.get().unwrap(), loc)
      }
      Call(cl) => {
        let ty = self.call(cl, c.func.loc);
        match &ty.kind {
          TyKind::Lambda(v) | TyKind::Func(v) => self.check_lambda_arg_param(&c.arg, v, loc),
          TyKind::Var | TyKind::Error => Ty::error(),
          _ => self.issue(loc, NotCallable(ty)),
        }
      }
      IndexSel(i) => { 
        let ty = self.expr(i.arr.as_ref());
        if ty.arr == 0 { return Ty::error() }
        self.expr(i.idx.as_ref());
        match &ty.arr_minus().kind {
          TyKind::Lambda(v) | TyKind::Func(v) => self.check_lambda_arg_param(&c.arg, v, loc),
          TyKind::Var | TyKind::Error => Ty::error(),
          _ => self.issue(loc, NotCallable(ty.arr_minus())),
        }
      }
      IntLit(_) | ReadInt(_) => self.issue(loc, NotCallable(Ty::int())), 
      BoolLit(_) => self.issue(loc, NotCallable(Ty::bool())), 
      StringLit(_) | ReadLine(_) => self.issue(loc, NotCallable(Ty::string())), 
      NullLit(_) => self.issue(loc, NotCallable(Ty::null())),
      Unary(u) => {
        let r = self.expr(&u.r);
        let (ty, op) = match u.op { UnOp::Neg => (Ty::int(), "-"), UnOp::Not => (Ty::bool(), "!"), };
        if r != ty { r.error_or(|| self.issue(loc, IncompatibleUnary { op, r })) }
        match &ty.kind {
          TyKind::Lambda(v) | TyKind::Func(v) => self.check_lambda_arg_param(&c.arg, v, loc),
          TyKind::Var | TyKind::Error => Ty::error(),
          _ => self.issue(loc, NotCallable(ty)),
        }
      }
      Binary(b) => {
        use BinOp::*;
        let (l, r) = (self.expr(&b.l), self.expr(&b.r));
        if l.kind == TyKind::Error || r.kind == TyKind::Error {
          // not using wildcard match, so that if we add new operators in the future, compiler can tell us
          match b.op { Add | Sub | Mul | Div | Mod => Ty::int(), And | Or | Eq | Ne | Lt | Le | Gt | Ge => Ty::bool() }
        } else {
          let (ret, ok) = match b.op {
            Add | Sub | Mul | Div | Mod => (Ty::int(), l == Ty::int() && r == Ty::int()),
            Lt | Le | Gt | Ge => (Ty::bool(), l == Ty::int() && r == Ty::int()),
            Eq | Ne => (Ty::bool(), l.assignable_to(r) || r.assignable_to(l)),
            And | Or => (Ty::bool(), l == Ty::bool() && r == Ty::bool())
          };
          if !ok { 
            self.issue(loc, IncompatibleBinary { l, op: b.op.to_op_str(), r }) 
          }
          self.issue(loc, NotCallable(ret))
        }
      }
      This(_) => {
        let ret = self.cur_class.unwrap();
        self.issue(loc, NotCallable(Ty::mk_obj(ret)))
      }
      NewClass(n) => if let Some(c) = self.scopes.lookup_class(n.name) {
        n.class.set(Some(c));
        self.issue(loc, NotCallable(Ty::mk_obj(c)))
      } else { self.issue(loc, NoSuchClass(n.name)) },
      NewArray(n) => {
        let len = self.expr(&n.len);
        if len != Ty::int() { len.error_or(|| self.issue(n.len.loc, NewArrayNotInt)) }
        let ret = self.ty(&n.elem, true);
        self.issue(loc, NotCallable(ret))
      }
      ClassTest(c) => {
        let src = self.expr(&c.expr);
        if !src.is_object() { src.error_or(|| self.issue(loc, NotObject(src))) }
        if let Some(cl) = self.scopes.lookup_class(c.name) {
          c.class.set(Some(cl));
          self.issue(loc, NotCallable(Ty::bool()))
        } else { self.issue(loc, NoSuchClass(c.name)) }
      }
      ClassCast(c) => {
        let src = self.expr(&c.expr);
        if !src.is_object() { src.error_or(|| self.issue(loc, NotObject(src))) }
        if let Some(cl) = self.scopes.lookup_class(c.name) {
          c.class.set(Some(cl));
          self.issue(loc, NotCallable(Ty::mk_obj(cl)))
        } else { self.issue(loc, NoSuchClass(c.name)) }
      }
    }
  }
}

impl<'a> TypePass<'a> {
  fn check_bool(&mut self, e: &'a Expr<'a>) {
    let ty = self.expr(e);
    if ty != Ty::bool() { ty.error_or(|| self.issue(e.loc, TestNotBool)) }
  }

  fn combine(&mut self, lhs: (bool, Ty<'a>), rhs: (bool, Ty<'a>), param: bool) -> (bool, Ty<'a>) {
    use TyKind::*;

    (lhs.0 || rhs.0, 
      match (lhs.1.kind, rhs.1.kind) {
        (Error, _) | (_, Error)=> Ty::error(),
        (Void, Void) => Ty::void(),
        (Void, _) => if lhs.0 { Ty::error() } else { rhs.1.clone() }
        (_, Void) => if rhs.0 { Ty::error() } else { lhs.1.clone() }
        _ => if lhs.1.arr == rhs.1.arr {
          if rhs.1.assignable_to(lhs.1) {
            if param == false { lhs.1.clone() } else { rhs.1.clone() }
          } else if lhs.1.assignable_to(rhs.1) {
            if param == false { rhs.1.clone() } else { lhs.1.clone() }
          } else {
            match (lhs.1.kind, rhs.1.kind) {
              (Object(Ref(c1)), Object(Ref(c2))) => {
                if param == false {
                  let mut c = c1;
                  loop {
                    if c2.extends(c) { break Ty::mk_obj(c); }
                    if let Some(p) = c.parent_ref.get() { c = p; } else { break Ty::error(); }
                  }
                } else { Ty::error() }
              }
              (Lambda(rp1), Lambda(rp2)) => {
                if rp1.len() == rp2.len() {
                  let (r1, p1, r2, p2) = (&rp1[0], &rp1[1..], &rp2[0], &rp2[1..]);
                  let ret_param_ty : Vec<Ty> = 
                    iter::once(self.combine((false, *r1), (false, *r2), param).1)
                      .chain(p1.iter().zip(p2.iter()).map(|(p1, p2)| self.combine((false, *p1), (false, *p2), !param).1)).collect();
                  for ty in ret_param_ty.iter() {
                    if ty.kind == TyKind::Error {
                      return (lhs.0 || rhs.0, Ty::error())
                    }
                  };
                  let ret_param_ty = self.alloc.ty.alloc_extend(ret_param_ty);
                  Ty::new(TyKind::Lambda(ret_param_ty))
                } else {
                  Ty::error()
                }
              },
              _ => Ty::error()
            }
          }
        } else { Ty::error() }
      }
    )
  }

  fn check_arg_param(&mut self, arg: &'a [Expr<'a>], ret_param: &[Ty<'a>], name: &'a str, loc: Loc) -> Ty<'a> {
    let (ret, param) = (ret_param[0], &ret_param[1..]);
    if param.len() != arg.len() {
      self.issue(loc, ArgcMismatch { name, expect: param.len() as u32, actual: arg.len() as u32 })
    }
    for (idx, arg0) in arg.iter().enumerate() {
      let arg = self.expr(arg0);
      if let Some(&param) = param.get(idx) {
        if !arg.assignable_to(param) {
          self.issue(arg0.loc, ArgMismatch { loc: idx as u32 + 1, arg, param })
        }
      }
    }
    ret
  }

  fn check_lambda_arg_param(&mut self, arg: &'a [Expr<'a>], ret_param: &[Ty<'a>], loc: Loc) -> Ty<'a> {
    let (ret, param) = (ret_param[0], &ret_param[1..]);
    if param.len() != arg.len() {
      self.issue(loc, LambdaArgcMismatch { expect: param.len() as u32, actual: arg.len() as u32 })
    }
    for (idx, arg0) in arg.iter().enumerate() {
      let arg = self.expr(arg0);
      if let Some(&param) = param.get(idx) {
        if !arg.assignable_to(param) {
          self.issue(arg0.loc, ArgMismatch { loc: idx as u32 + 1, arg, param })
        }
      }
    }
    ret
  }

  fn in_lambda(&self) -> bool {
    !self.cur_lambda.is_none() && (self.cur_func.is_none() || self.cur_lambda.unwrap().loc > self.cur_func.unwrap().loc)
  }

  fn in_func(&self) -> bool {
    !self.cur_func.is_none() && (self.cur_lambda.is_none() || self.cur_func.unwrap().loc > self.cur_lambda.unwrap().loc)
  }

  fn is_lvalue(&self, loc: Loc) -> bool {
    self.cur_assign.is_none() == false && loc < self.cur_assign.unwrap()
  }

  fn is_rvalue(&self, loc: Loc) -> bool {
    self.cur_assign.is_none() == false && loc > self.cur_assign.unwrap()
  }
}