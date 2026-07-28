module

public import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.DCE.dce
import Veir.Rewriter.WfRewriter
import Veir.Interfaces.FunctionInterfaces

namespace Veir

/-! ## Coercing function boundaries to `!riscv.reg`

  Before removing round-trip casts, we rewrite each `func.func` and
  `llvm.func`'s i32- and i64- and pointer-typed arguments and return
  values to `!riscv.reg`, inserting `unrealized_conversion_cast`s to
  bridge to/from the original integer types.
-/

def isRegCoercibleType (t : TypeAttr) : Bool :=
  match t.val with
  | .integerType x => x.bitwidth == 64 || x.bitwidth == 32
  | .llvmPointerType _ => true
  | _ => false

/-- The return-terminator opcode paired with a function op (`func.return` for
    `func.func`, `llvm.return` for `llvm.func`). -/
def returnOpCodeFor : OpCode → OpCode
  | .llvm .func => .llvm .return
  | _ => .func .return

set_option warn.sorry false in
/-- Coerce one function's `i32`/`i64` arguments and return values to `!riscv.reg`,
    inserting bridging casts and rewriting the `function_type` to match. Handles both
    `func.func` and `llvm.func`. -/
def coerceFunction (ctx : WfIRContext OpCode) (funcOp : OperationPtr) :
    ExceptT String IO (WfIRContext OpCode) := do
  -- Shadow the parameter: from here on `ctx` always names the latest version, with no
  -- separate old binding left around to second-guess.
  let mut ctx := ctx
  let some entry := FunctionOpInterface.getEntryBlock? funcOp ctx.raw | return ctx
  let returnCode := returnOpCodeFor (funcOp.getOpType! ctx.raw)
  -- Default the output types to the currently-declared ones, then flip coerced positions.
  -- This preserves non-integer results and `llvm.func`'s `void` return.
  let mut outputs : Array Attribute := FunctionOpInterface.getResultTypes! funcOp ctx.raw
  -- (1) Coerce entry-block arguments (the function parameters). This mirrors the
  --     block-argument coercion in `isel-br-riscv64`, which skips entry blocks.
  let mut inputs : Array Attribute := #[]
  for i in List.range (entry.getNumArguments! ctx.raw) do
    let bap : BlockArgumentPtr := { block := entry, index := i }
    let origType := (ValuePtr.blockArgument bap).getType! ctx.raw
    if isRegCoercibleType origType then
      ctx := WfRewriter.setType ctx bap RegisterType.mk sorry
      let ip := InsertPoint.atStart entry ctx.raw sorry
      let some (ctx', cast) := WfRewriter.createOp ctx
        (.builtin .unrealized_conversion_cast) #[origType] #[] #[] #[] default (some ip)
        sorry sorry sorry sorry | return ctx
      let ctx' := WfRewriter.replaceValue ctx' bap (cast.getResult 0) sorry sorry sorry
      ctx := WfRewriter.pushOperand ctx' cast bap sorry sorry
      inputs := inputs.push (.registerType ⟨none⟩)
    else
      inputs := inputs.push origType.val
  -- (2) Coerce the operands of every return terminator in this function.
  let returnOps := ctx.raw.operations.keys.filter fun o =>
    o.getOpType! ctx.raw == returnCode &&
      o.getParentOp! ctx.raw == some funcOp
  for retOp in returnOps do
    for j in List.range (retOp.getNumOperands! ctx.raw) do
      let opVal := retOp.getOperand! ctx.raw j
      let opType := opVal.getType! ctx.raw
      if isRegCoercibleType opType then
        let some (ctx', cast) := WfRewriter.createOp ctx
          (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[opVal] #[] #[] default
          (some (InsertPoint.before retOp)) sorry sorry sorry sorry | return ctx
        ctx := WfRewriter.replaceOperand ctx' ⟨retOp, j⟩ (cast.getResult 0) sorry sorry
        -- The `j`-th operand maps to the `j`-th declared result: the verifier guarantees
        -- a return's operand count equals the function's declared result count.
        outputs := outputs.set! j (.registerType ⟨none⟩)
  -- (3) Rewrite the function_type to reflect the coerced boundary types.
  ctx := FunctionOpInterface.setFunctionType! ctx funcOp inputs outputs
  return ctx

def coerceFunctionBoundaries (ctx : WfIRContext OpCode) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut ctx := ctx
  let funcOps := ctx.raw.operations.keys.filter fun o =>
    match o.getOpType! ctx.raw with
    | .func .func | .llvm .func => true
    | _ => false
  for funcOp in funcOps do
    ctx ← coerceFunction ctx funcOp
  return ctx


def CoerceFunctionBoundariesToRiscvRegPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let ctx ← coerceFunctionBoundaries ctx
  match RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern #[eliminateDeadOp]) ctx with
  | none => throw "Error while applying DCE after cast reconciliation"
  | some ctx => pure ctx

public def CoerceFunctionBoundariesToRiscvRegPass : Pass OpCode :=
  { name := "coerce-function-boundaries-to-riscv-reg"
    description := "Coerce function boundaries to `!riscv.reg`."
    run := CoerceFunctionBoundariesToRiscvRegPass.impl }
