import Veir.Interfaces.CallInterfaces
import Veir.Input
import UnitTest.Helpers

open Veir
open Veir.Input

/-! ## Callees -/

/-- The callee of the operation in `s`. -/
private def parseCallee? (s : String) : Option (CallInterfaceCallable ValuePtr) :=
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

/- A direct call resolves to the symbol it names, and an indirect call to the operation defining
   its callee. -/

#guard (CallOp.of? directCall ctx).bind (·.resolveCallable?) = some func
#guard (CallOp.of? indirectCall ctx).bind (·.resolveCallable?) = some addressOf

/-! ## Argument Operands -/

/-- The names of the arguments passed by the call in `s`, which may use `%a`, `%b` and `%p`. -/
private def parseArgOperands? (s : String) : Option (Array String) :=
  let (ctx, module) := parseSourceString! (verifyAfterParse := false) (r#""builtin.module"() ({
  ^bb0(%a: i32, %b: i32, %p: !llvm.ptr):
    "# ++ s ++ r#"
  }) : () -> ()"#).toUTF8
  (CallOp.of? (module.body! ctx.raw) ctx.raw).bind fun callOp =>
    callOp.getArgOperands.mapM fun
      | .blockArgument arg => #["a", "b", "p"][arg.index]?
      | .opResult _ => none

-- A direct call passes all its operands.

#guard parseArgOperands? r#""func.call"(%a, %b) <{callee = @f}> : (i32, i32) -> ()"# =
  some #["a", "b"]
#guard parseArgOperands? r#""riscv_cf.call"(%a, %b) <{callee = @f}> : (i32, i32) -> ()"# =
  some #["a", "b"]

-- An indirect call does not pass its callee.

#guard parseArgOperands? r#""riscv_cf.call"(%p, %a) : (!llvm.ptr, i32) -> ()"# = some #["a"]
#guard parseArgOperands? r#""llvm.call"(%p, %a) <{op_bundle_sizes = array<i32>,
  operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, i32) -> ()"# = some #["a"]

-- `%b` belongs to an operand bundle, which is information for the optimizer, not an argument.

#guard parseArgOperands? r#""llvm.call"(%a, %b) <{callee = @f, op_bundle_sizes = array<i32: 1>,
  op_bundle_tags = ["align"], operandSegmentSizes = array<i32: 1, 1>}> : (i32, i32) -> ()"# =
  some #["a"]

-- `%b` is an operand of an affine map computing a size in the result type, not an argument.

#guard parseArgOperands? r#""function.call"(%a, %b) <{callee = @f, mapOpGroupSizes = array<i32: 1>,
  numDimsPerMap = array<i32: 1>, operandSegmentSizes = array<i32: 1, 1>}> : (i32, i32) -> ()"# =
  some #["a"]
