use crate::{TypeCk, TypeCkTrait};
use common::{ErrorKind::*, Ref, MAIN_CLASS, MAIN_METHOD, NO_LOC, HashMap, HashSet};
use syntax::{ast::*, ScopeOwner, Symbol, Ty};
use std::{ops::{Deref, DerefMut}, iter};
use hashbrown::hash_map::Entry;

pub(crate) struct SymbolPass<'a>(pub TypeCk<'a>);

// some boilerplate code...
impl<'a> Deref for SymbolPass<'a> {
  type Target = TypeCk<'a>;
  fn deref(&self) -> &Self::Target { &self.0 }
}

impl<'a> DerefMut for SymbolPass<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl<'a> SymbolPass<'a> {
  pub fn program(&mut self, p: &'a Program<'a>) {
    // the global scope is already opened, so no need to open it here
    for c in &p.class {
      if c.name == MAIN_CLASS && c.abstract_ {
        self.issue(NO_LOC, NoMainClass)
      } else if let Some(prev) = self.scopes.lookup_class(c.name) {
        self.issue(c.loc, ConflictDeclaration { prev: prev.loc, name: c.name })
      } else {
        self.scopes.declare(Symbol::Class(c));
      }
    }
    for c in &p.class {
      if let Some(p) = c.parent {
        c.parent_ref.set(self.scopes.lookup_class(p));
        if c.parent_ref.get().is_none() { self.issue(c.loc, NoSuchClass(p)) }
      }
    }
    // detect cyclic inheritance
    let mut vis = HashMap::new();
    for (idx, c) in p.class.iter().enumerate() {
      let mut c = *c;
      let mut last = c; // this assignment is useless, the value of `last` never comes from it when used
      loop {
        match vis.entry(Ref(c)) {
          Entry::Vacant(v) => {
            v.insert(idx);
            if let Some(p) = c.parent_ref.get() { (last = c, c = p); } else { break; }
          }
          Entry::Occupied(o) => {
            if *o.get() == idx { self.issue(last.loc, CyclicInheritance) }
            break;
          }
        }
      }
    }
    // errors related to inheritance are considered as fatal errors, return after these checks if a error occurred
    if !self.errors.0.is_empty() { return; }
    let mut checked = HashSet::new();
    for c in &p.class {
      self.class_def(c, &mut checked);
      if c.name == MAIN_CLASS { p.main.set(Some(c)); }
    }
    if p.main.get().map(|c| match c.scope.borrow().get(MAIN_METHOD) {
      Some(Symbol::Func(main)) if main.static_ && main.param.is_empty() && main.ret_ty() == Ty::void() => false, _ => true
    }).unwrap_or(true) { self.issue(NO_LOC, NoMainClass) }
    for c in &p.class {
      if !c.abstract_ && c.ab_unoverload().len() > 0 {
        self.issue(c.loc, NotOverrideAllAbstract(c.name))
      } 
    }
  }

  fn class_def(&mut self, c: &'a ClassDef<'a>, checked: &mut HashSet<Ref<'a, ClassDef<'a>>>) {
    if !checked.insert(Ref(c)) { return; }
    if let Some(p) = c.parent_ref.get() { self.class_def(p, checked); }
    self.cur_class = Some(c);
    self.scoped(ScopeOwner::Class(c), |s| for f in &c.field {
      match f { FieldDef::FuncDef(f) => s.func_def(f), FieldDef::VarDef(v) => s.var_def(v) };
    });
  }

  fn func_def(&mut self, f: &'a FuncDef<'a>) {
    let ret_ty = self.ty(&f.ret, false);
    self.scoped(ScopeOwner::Param(f), |s| {
      if !f.static_ { s.scopes.declare(Symbol::This(f)); }
      for v in &f.param { s.var_def(v); }
      if f.body.is_none() == false {
        s.block(&f.body.as_ref().unwrap());
      }
    });
    let ret_param_ty = iter::once(ret_ty).chain(f.param.iter().map(|v| v.ty.get()));
    let ret_param_ty = self.alloc.ty.alloc_extend(ret_param_ty);
    f.ret_param_ty.set(Some(ret_param_ty));
    f.class.set(self.cur_class);
    let ok = if let Some((sym, owner)) = self.scopes.lookup(f.name) {
      match (self.scopes.cur_owner(), owner) {
        (ScopeOwner::Class(c), ScopeOwner::Class(p)) if Ref(c) != Ref(p) => {
          match sym {
            Symbol::Func(pf) => {
              if f.static_ || pf.static_ || (f.abstract_ && !pf.abstract_) {
                self.issue(f.loc, ConflictDeclaration { prev: pf.loc, name: f.name })
              } else if !Ty::mk_func(f).assignable_to(Ty::mk_func(pf)) {
                self.issue(f.loc, OverrideMismatch { func: f.name, p: p.name })
              } else { true }
            }
            _ => self.issue(f.loc, ConflictDeclaration { prev: sym.loc(), name: f.name }),
          }
        }
        _ => self.issue(f.loc, ConflictDeclaration { prev: sym.loc(), name: f.name }),
      }
    } else { true };
    if ok { 
      f.owner.set(Some(self.scopes.cur_owner()));
      self.scopes.declare(Symbol::Func(f)); 
    }
  }

  fn var_def(&mut self, v: &'a VarDef<'a>) {
    if v.syn_ty.is_none() == false {
      v.ty.set(self.ty(&v.syn_ty.as_ref().unwrap(), false));
      if v.ty.get() == Ty::void() { self.issue(v.loc, VoidVar(v.name)) }
    } else {
      v.ty.set(Ty::var())
    }
    let ok = if let Some((sym, owner)) = self.scopes.lookup(v.name) {
      match (self.scopes.cur_owner(), owner) {
        (ScopeOwner::Class(c1), ScopeOwner::Class(c2)) if Ref(c1) != Ref(c2) && sym.is_var() =>
          self.issue(v.loc, OverrideVar(v.name)),
        (ScopeOwner::Class(_), ScopeOwner::Class(_)) | (_, ScopeOwner::Param(_)) | (_, ScopeOwner::Local(_)) | (_, ScopeOwner::Lambda(_)) =>
          self.issue(v.loc, ConflictDeclaration { prev: sym.loc(), name: v.name }),
        _ => true,
      }
    } else { true };
    if ok {
      v.owner.set(Some(self.scopes.cur_owner()));
      self.scopes.declare(Symbol::Var(v));
    }
    if !v.init().is_none() {
      self.expr(v.init().unwrap());
    }
  }

  fn block(&mut self, b: &'a Block<'a>) {
    self.scoped(ScopeOwner::Local(b), |s| for st in &b.stmt { s.stmt(st); });
  }

  fn lambda(&mut self, f: &'a Lambda<'a>) {
    self.scoped(ScopeOwner::Lambda(f), |s| {
      for v in &f.param { s.var_def(v); }
      if f.body.is_right() {
        s.block(&f.body.as_ref().right().unwrap());
      } else {
        s.scoped(ScopeOwner::LambdaExpr(&f.body.as_ref().left().unwrap()), |s| {
          s.expr(&f.body.as_ref().left().unwrap());
        });
      }
    });
    self.scopes.declare(Symbol::Lambda(f));
  }

  // fn varsel(&mut self, v: &'a VarSel<'a>) {
    // self.scoped(ScopeOwner::Lambda(f), |s| {
    //   for v in &f.param { s.var_def(v); }
    //   if f.body.is_right() {
    //     s.block(&f.body.as_ref().right().unwrap());
    //   } else {
    //     s.scoped(ScopeOwner::LambdaExpr(&f.body.as_ref().left().unwrap()), |s| {
    //       s.expr(&f.body.as_ref().left().unwrap());
    //     });
    //   }
    // });
    // self.scopes.declare(Symbol::Lambda(f));
  // }

  // fn call(&mut self, c: &'a Call<'a>) {
  //   match &c.func.kind {
  //     ExprKind::Lambda(f) => self.lambda(f),
  //     ExprKind::Call(c) => self.call(c),
  //     _ => {},
  //   }
  // }

  fn expr(&mut self, e: &'a Expr<'a>) {
    use ExprKind::*;
    match &e.kind {
      Lambda(f) => self.lambda(f),
      Call(c) => {
        self.expr(c.func.as_ref());
        for e in c.arg.iter() { self.expr(e) }
      }
      VarSel(v) => { 
        if !v.owner.is_none() { self.expr(v.owner.as_ref().unwrap().as_ref()) }
      }
      IndexSel(s) => {
        self.expr(s.arr.as_ref());
        self.expr(s.idx.as_ref());
      }
      Unary(u) => {
        self.expr(u.r.as_ref());
      }
      Binary(b) => { 
        self.expr(b.l.as_ref());
        self.expr(b.r.as_ref());
      }
      NewArray(a) => {
        self.expr(a.len.as_ref());
      }
      ClassTest(ct) => { 
        self.expr(ct.expr.as_ref()) 
      }
      ClassCast(cc) => {
        self.expr(cc.expr.as_ref()) 
      }
      _ => {}
    }
  }

  fn stmt(&mut self, s: &'a Stmt<'a>) {
    match &s.kind {
      StmtKind::LocalVarDef(v) => self.var_def(v),
      StmtKind::If(i) => {
        self.block(&i.on_true);
        if let Some(of) = &i.on_false { self.block(of); }
      }
      StmtKind::While(w) => self.block(&w.body),
      StmtKind::For(f) => self.scoped(ScopeOwner::Local(&f.body), |s| {
        s.stmt(&f.init);
        s.stmt(&f.update);
        for st in &f.body.stmt { s.stmt(st); }
      }),
      StmtKind::Block(b) => self.block(b),
      StmtKind::Return(r) => if !r.is_none() { self.expr(r.as_ref().unwrap()) },
      StmtKind::Assign(a) => { self.expr(&a.dst); self.expr(&a.src) }
      StmtKind::ExprEval(e) => { self.expr(e) }
      StmtKind::Print(p) => { 
        for e in p.iter() { self.expr(e) }
      }
      _ => {}
    };
  }
}