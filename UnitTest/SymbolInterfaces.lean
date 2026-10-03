import Veir.Interfaces.SymbolInterfaces
import Veir.Input

open Veir
open Veir.Input

/-- The name of the symbol defined by the operation in `s`. -/
private def parseSymName? (s : String) : Option String :=
  let (ctx, op) := parseSourceString! s.toUTF8 (verifyAfterParse := false)
  (SymbolOp.cast? op ctx.raw).map (String.fromUTF8! ·.getSymName.value)

/- Functions are symbols, and so are operations such as globals that are not functions. -/

#guard parseSymName? r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
}) : () -> ()"# == some "f"
#guard parseSymName? r#""llvm.mlir.global"() <{global_type = i32, linkage = #llvm.linkage<internal>, sym_name = "x"}> ({
}) : () -> ()"# == some "x"

/- A `pdl.pattern` is an optional symbol: as in MLIR, it is only a symbol when it has a name. -/

#guard parseSymName? r#""pdl.pattern"() <{benefit = 1 : i16, sym_name = "p"}> ({
}) : () -> ()"# == some "p"
#guard parseSymName? r#""pdl.pattern"() <{benefit = 1 : i16}> ({
}) : () -> ()"# == none

/- An operation which is not a symbol. -/

#guard parseSymName? r#"%0 = "arith.constant"() <{value = 0 : i32}> : () -> i32"# == none
