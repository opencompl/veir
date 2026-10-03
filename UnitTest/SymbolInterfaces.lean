import Veir.Interfaces.SymbolInterfaces
import Veir.Input

open Veir
open Veir.Input

/-! ## Symbols -/

/-- The name of the symbol defined by the operation in `s`. -/
private def parseSymName? (s : String) : Option String :=
  let (ctx, op) := parseSourceString! s.toUTF8 (verifyAfterParse := false)
  (SymbolOp.of? op ctx.raw).map (String.fromUTF8! ·.getSymName.value)

-- Functions are symbols, and so are operations such as globals that are not functions.

#guard parseSymName? r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
}) : () -> ()"# = some "f"
#guard parseSymName? r#""llvm.mlir.global"() <{global_type = i32, linkage = #llvm.linkage<internal>, sym_name = "x"}> ({
}) : () -> ()"# = some "x"

-- `pdl.pattern` and `builtin.module` are optional symbols: as in MLIR, they are only symbols
-- when they have a name.

#guard parseSymName? r#""pdl.pattern"() <{benefit = 1 : i16, sym_name = "p"}> ({
}) : () -> ()"# = some "p"
#guard parseSymName? r#""pdl.pattern"() <{benefit = 1 : i16}> ({
}) : () -> ()"# = none

#guard parseSymName? r#""builtin.module"() <{sym_name = "m"}> ({
}) : () -> ()"# = some "m"
#guard parseSymName? r#""builtin.module"() ({
}) : () -> ()"# = none

-- An operation which is not a symbol.

#guard parseSymName? r#"%0 = "arith.constant"() <{value = 0 : i32}> : () -> i32"# = none

/-! ## Symbol Tables -/

/--
A module with a function `caller` calling a function `callee`, and a comdat, which is a nested
symbol table with a selector.
-/
private def parsed := parseSourceString! r#""builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "caller"}> ({
    "func.call"() <{callee = @callee}> : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{function_type = () -> (), sym_name = "callee"}> ({
    "func.return"() : () -> ()
  }) : () -> ()
  "llvm.comdat"() <{sym_name = "comdat"}> ({
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "selector"}> : () -> ()
  }) : () -> ()
}) : () -> ()"#.toUTF8

private def ctx := parsed.1.raw

/-- The first operation in the body of `op`. -/
private def Veir.OperationPtr.body! (op : OperationPtr) : OperationPtr :=
  (((op.getRegion! ctx 0).get! ctx).firstBlock.get!.get! ctx).firstOp.get!

/-- The operation following `op` in its block. -/
private def Veir.OperationPtr.next! (op : OperationPtr) : OperationPtr :=
  (op.get! ctx).next.get!

private def moduleOp := parsed.2
private def caller := moduleOp.body!
private def callOp := caller.body!
private def callee := caller.next!
private def comdat := callee.next!
private def selector := comdat.body!

-- Modules and comdats are symbol tables, and functions are not.

#guard moduleOp.isSymbolTable ctx
#guard comdat.isSymbolTable ctx
#guard !caller.isSymbolTable ctx

-- A symbol table defines the symbols directly in its body, but not those of nested tables.

#guard moduleOp.lookupSymbolIn! ctx ⟨"callee".toUTF8⟩ = some callee
-- TODO: Implement lookup for nested references (`@comdat::@selector`)
#guard moduleOp.lookupSymbolIn! ctx ⟨"selector".toUTF8⟩ = none
#guard comdat.lookupSymbolIn! ctx ⟨"selector".toUTF8⟩ = some selector
#guard moduleOp.lookupSymbolIn! ctx ⟨"unknown".toUTF8⟩ = none

-- An operation is its own nearest symbol table if it is one.

#guard (callOp.getNearestSymbolTable? ctx).map (·.val) = some moduleOp
#guard (selector.getNearestSymbolTable? ctx).map (·.val) = some comdat
#guard (comdat.getNearestSymbolTable? ctx).map (·.val) = some comdat

-- Lookup uses the nearest symbol table only, so `callee` is not visible from the comdat.

#guard callOp.lookupNearestSymbolFrom? ctx ⟨"callee".toUTF8⟩ = some callee
#guard selector.lookupNearestSymbolFrom? ctx ⟨"callee".toUTF8⟩ = none
