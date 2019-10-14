#![feature(result_map_or_else)]

pub mod test_util;

use common::{IndentPrinter, Errors};
use syntax::{ASTAlloc, Ty, parser};

pub use test_util::*;

#[derive(Eq, PartialEq, Copy, Clone)]
pub enum Stage { Parse, TypeCk, Tac, TacOpt, Asm }

#[derive(Copy, Clone)]
pub enum Parser { LL, LR }

#[derive(Copy, Clone)]
pub struct CompileCfg {
  pub stage: Stage,
  pub parser: Parser,
}

#[derive(Default)]
pub struct Alloc<'a> {
  ast: ASTAlloc<'a>,
}

// it is recommended to use this function to debug your compiler
// `code` can be provided by hard-coded string literal, `cfg` can be provided by `Pa::Pax.to_cfg()`
pub fn compile<'a>(code: &'a str, alloc: &'a Alloc<'a>, cfg: CompileCfg) -> Result<String, Errors<'a, Ty<'a>>> {
  let mut p = IndentPrinter::default();
  let pr = match cfg.parser {
    Parser::LL => unimplemented!(),
    Parser::LR => parser::work(code, &alloc.ast)?,
  };
  if cfg.stage == Stage::Parse {
    print::ast::program(&pr, &mut p);
    return Ok(p.finish());
  }
  unimplemented!()
}
