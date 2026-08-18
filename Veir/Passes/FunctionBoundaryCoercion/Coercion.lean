module

public import Veir.Pass
import Veir.Passes.DCE.dce

namespace Veir

/-! ## Coercing function boundaries

  Rewrite each `func.func`/`llvm.func`'s arguments and return values to a coerced type,
  inserting`unrealized_conversion_cast`s to bridge to/from the original types.

  The coercion applied is selected by a `BoundaryCoercion` flag;
  each variant is  exposed as its own pass:
  - `.riscvReg`: i32-, i64-, and pointer-typed boundaries become `!riscv.reg`.
  - `.modArithToInt legalizeWidth`: `!mod_arith.int<q : iN>`-typed boundaries become `i(legalizeWidth N)`
-/

/-- Selects which boundary coercion the shared implementation applies. -/
inductive BoundaryCoercion where
  | riscvReg
  | modArithToInt (legalizeWidth : Nat → Nat)

/-- The type a boundary value of type `t` is coerced to, or `none` to leave it alone. -/
def BoundaryCoercion.target : BoundaryCoercion → TypeAttr → Option TypeAttr
  | .riscvReg, t =>
    match t.val with
    | .integerType x =>
      if x.bitwidth == 64 || x.bitwidth == 32 then some (RegisterType.mk : TypeAttr) else none
    | .llvmPointerType _ => some (RegisterType.mk : TypeAttr)
    | _ => none
  | .modArithToInt legalizeWidth, t =>
    match t.val with
    | .modArithType mt => some (IntegerType.mk (legalizeWidth mt.bitwidth) : TypeAttr)
    | _ => none

/-- The return-terminator opcode paired with a function op (`func.return` for
    `func.func`, `llvm.return` for `llvm.func`). -/
def returnOpCodeFor : OpCode → OpCode
  | .llvm .func => .llvm .return
  | _ => .func .return

set_option warn.sorry false in
/-- Coerce one function's arguments and return values as dictated by `coercion`,
    inserting bridging casts and rewriting the `function_type` to match. Handles both
    `func.func` and `llvm.func`. -/
def coerceFunction (coercion : BoundaryCoercion) (ctx : WfIRContext OpCode)
    (funcOp : OperationPtr) : ExceptT String IO (WfIRContext OpCode) := do
  -- Shadow the parameter: from here on `ctx` always names the latest version, with no
  -- separate old binding left around to second-guess.
  let mut ctx := ctx
  let some entry := FunctionOpInterface.getEntryBlock? funcOp ctx.raw | return ctx
  let returnCode := returnOpCodeFor (funcOp.getOpType! ctx.raw)
  -- Default the output types to the currently-declared ones, then flip coerced positions.
  -- This preserves uncoerced results and `llvm.func`'s `void` return.
  let mut outputs : Array Attribute := FunctionOpInterface.getResultTypes! funcOp ctx.raw
  -- (1) Coerce entry-block arguments (the function parameters). This mirrors the
  --     block-argument coercion in `isel-br-riscv64`, which skips entry blocks.
  let mut inputs : Array Attribute := #[]
  for i in List.range (entry.getNumArguments! ctx.raw) do
    let bap : BlockArgumentPtr := { block := entry, index := i }
    let origType := (ValuePtr.blockArgument bap).getType! ctx.raw
    match coercion.target origType with
    | some newType =>
      ctx := WfRewriter.setType ctx bap newType sorry
      let ip := InsertPoint.atStart entry ctx.raw sorry
      let some (ctx', cast) := WfRewriter.createOp ctx
        Builtin.unrealized_conversion_cast #[origType] #[] #[] #[] default (some ip)
        sorry sorry sorry sorry | return ctx
      let ctx' := WfRewriter.replaceValue ctx' bap (cast.getResult 0) sorry sorry sorry
      ctx := WfRewriter.pushOperand ctx' cast bap sorry sorry
      inputs := inputs.push newType.val
    | none =>
      inputs := inputs.push origType.val
  -- (2) Coerce the operands of every return terminator in this function.
  let returnOps := ctx.raw.operations.keys.filter fun o =>
    o.getOpType! ctx.raw == returnCode &&
      o.getParentOp! ctx.raw == some funcOp
  for retOp in returnOps do
    for j in List.range (retOp.getNumOperands! ctx.raw) do
      let opVal := retOp.getOperand! ctx.raw j
      let opType := opVal.getType! ctx.raw
      match coercion.target opType with
      | some newType =>
        let some (ctx', cast) := WfRewriter.createOp ctx
          Builtin.unrealized_conversion_cast #[newType] #[opVal] #[] #[] default
          (some (InsertPoint.before retOp)) sorry sorry sorry sorry | return ctx
        ctx := WfRewriter.replaceOperand ctx' ⟨retOp, j⟩ (cast.getResult 0) sorry sorry
        -- The `j`-th operand maps to the `j`-th declared result: the verifier guarantees
        -- a return's operand count equals the function's declared result count.
        outputs := outputs.set! j newType.val
      | none => pure ()
  -- (3) Rewrite the function_type to reflect the coerced boundary types.
  ctx := FunctionOpInterface.setFunctionType! ctx funcOp inputs outputs
  return ctx

def coerceFunctionBoundaries (coercion : BoundaryCoercion) (ctx : WfIRContext OpCode) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut ctx := ctx
  let funcOps := ctx.raw.operations.keys.filter fun o => o.isFunctionLike ctx.raw
  for funcOp in funcOps do
    ctx ← coerceFunction coercion ctx funcOp
  return ctx


def CoerceFunctionBoundariesPass.impl (coercion : BoundaryCoercion) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let ctx ← coerceFunctionBoundaries coercion ctx
  match RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern #[eliminateDeadOp]) ctx with
  | none => throw "Error while applying DCE after function boundary coercion"
  | some ctx => pure ctx

public def CoerceFunctionBoundariesToRiscvRegPass : Pass OpCode :=
  { name := "coerce-function-boundaries-to-riscv-reg"
    description := "Coerce i32/i64/pointer function boundaries to `!riscv.reg`."
    run := fun _ => CoerceFunctionBoundariesPass.impl .riscvReg }

public def CoerceModArithFunctionBoundariesPass : Pass OpCode :=
  { name := "coerce-mod-arith-function-boundaries"
    description := "Coerce `!mod_arith.int` function boundaries to their storage integer type."
    options := .ofList [
      ("pow2-width", { description := "Widen the storage integer type to a power-of-two bitwidth." })]
    run := fun options =>
      CoerceFunctionBoundariesPass.impl
        (.modArithToInt
          (if (options.get? "pow2-width").getD false then Nat.nextPowerOfTwo else id)) }
