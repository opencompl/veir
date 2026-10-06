import Veir.Interfaces.CallInterfaces
import Veir.Input
import UnitTest.Helpers

open Veir
open Veir.Input

/-! ## Callees -/

/-- The callee of the operation in `s`. -/
private def parseCallee? (s : String) : Option CallInterfaceCallable :=
  let (ctx, op) := parseSourceString! s.toUTF8 (verifyAfterParse := false)
  (CallOp.of? op ctx.raw).bind (·.getCallableForCallee?)

-- A direct call names its callee with a symbol.

#guard parseCallee? r#""func.call"() <{callee = @f}> : () -> ()"# = some (.symbol ⟨"@f"⟩)
#guard parseCallee? r#""llvm.call"() <{callee = @f}> : () -> ()"# = some (.symbol ⟨"@f"⟩)

-- An operation which is not a call.

#guard parseCallee? r#""func.return"() : () -> ()"# = none

/-! ## Resolving Callees -/

/-- A function `f` calling itself directly, and indirectly through its address. -/
private def parsed := parseSourceString! r#""builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<void ()>}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @f}> : () -> !llvm.ptr
    "llvm.call"() <{callee = @f}> : () -> ()
    "llvm.call"(%0) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#.toUTF8

private def ctx := parsed.1.raw

private def func := parsed.2.body! ctx
private def addressOf := func.body! ctx
private def directCall := addressOf.next! ctx
private def indirectCall := directCall.next! ctx

-- A direct call resolves to the symbol it names, and an indirect call to the operation defining
-- its callee.

#guard (CallOp.of? directCall ctx).bind (·.resolveCallable?) = some func
#guard (CallOp.of? indirectCall ctx).bind (·.resolveCallable?) = some addressOf
