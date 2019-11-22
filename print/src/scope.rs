use common::{IndentPrinter, IgnoreResult};
use syntax::{ast::*, Scope};
use std::fmt::Write;

fn show_scope(s: &Scope, p: &mut IndentPrinter) {
  let mut s = s.iter().map(|(_, &sym)| sym).collect::<Vec<_>>();
  s.sort_unstable_by_key(|x| x.loc());
  if s.is_empty() { write!(p, "<empty>").ignore(); } else { for s in s { write!(p, "{:?}", s).ignore(); } }
}

pub fn program(pr: &Program, p: &mut IndentPrinter) {
  write!(p, "GLOBAL SCOPE:").ignore();
  p.indent(|p| {
    show_scope(&pr.scope.borrow(), p);
    for c in &pr.class { class_def(c, p); }
  });
}

pub fn class_def(c: &ClassDef, p: &mut IndentPrinter) {
  write!(p, "CLASS SCOPE OF '{}':", c.name).ignore();
  p.indent(|p| {
    show_scope(&c.scope.borrow(), p);
    for f in &c.field {
      if let FieldDef::FuncDef(f) = f { func_def(f, p); }
    }
  });
}

pub fn func_def(f: &FuncDef, p: &mut IndentPrinter) {
  write!(p, "FORMAL SCOPE OF '{}':", f.name).ignore();
  p.indent(|p| {
    show_scope(&f.scope.borrow(), p);
    if f.body.is_none() == false {
      block(&f.body.as_ref().unwrap(), p);
    }
  });
}

pub fn block(b: &Block, p: &mut IndentPrinter) {
  write!(p, "LOCAL SCOPE:").ignore();
  p.indent(|p| {
    show_scope(&b.scope.borrow(), p);
    for s in &b.stmt {
      match &s.kind {
        StmtKind::Assign(a) => { expr(&a.dst, p); expr(&a.src, p); }
        StmtKind::Print(pt) => for (_, e) in pt.iter().enumerate() { expr(e, p) },
        StmtKind::ExprEval(e) => expr(e, p),
        StmtKind::LocalVarDef(v) => if !v.init().is_none() { expr(v.init().unwrap(), p) },
        StmtKind::If(i) => {
          block(&i.on_true, p);
          if let Some(on_false) = &i.on_false { block(on_false, p); }
        }
        StmtKind::While(w) => block(&w.body, p),
        StmtKind::For(f) => block(&f.body, p),
        StmtKind::Block(b) => block(b, p),
        StmtKind::Return(r) => if !r.is_none() { expr(r.as_ref().unwrap(), p) },
        _ => {}
      }
    }
  });
}

pub fn expr(e: &Expr, p: &mut IndentPrinter) {
  use ExprKind::*;
  match &e.kind {
    Lambda(f) => lambda(f, p),
    IndexSel(s) => {
      expr(s.arr.as_ref(), p);
      expr(s.idx.as_ref(), p);
    }
    Call(c) => { 
      expr(c.func.as_ref(), p);
      for e in c.arg.iter() { expr(e, p) }
    } 
    VarSel(v) => { 
      if !v.owner.is_none() { expr(v.owner.as_ref().unwrap().as_ref(), p) }
    }
    Unary(u) => {
      expr(u.r.as_ref(), p);
    }
    Binary(b) => { 
      expr(b.l.as_ref(), p);
      expr(b.r.as_ref(), p);
    }
    NewArray(a) => {
      expr(a.len.as_ref(), p);
    }
    ClassTest(ct) => { 
      expr(ct.expr.as_ref(), p);
    }
    ClassCast(cc) => {
      expr(cc.expr.as_ref(), p);
    }
    _ => {},
  }
}

pub fn lambda(f: &Lambda, p: &mut IndentPrinter) {
  write!(p, "FORMAL SCOPE OF '{}':", f.name).ignore();
  p.indent(|p| {
    show_scope(&f.scope.borrow(), p);
    if f.body.is_left() {
      write!(p, "LOCAL SCOPE:").ignore();
      p.indent(|p| {
        show_scope(&f.body.as_ref().left().unwrap().scope.borrow(), p);
        match &f.body.as_ref().left().unwrap().kind {
          ExprKind::Lambda(_f) => lambda(_f, p),
          _ => {},
        }
      });
    } else {
      block(&f.body.as_ref().right().unwrap(), p); 
    }
  });
}