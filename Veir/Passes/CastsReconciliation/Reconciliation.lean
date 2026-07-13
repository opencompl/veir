import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.DCE.dce
import Veir.Rewriter.WfRewriter
import Veir.Properties
import Veir.Interfaces.FunctionInterfaces

namespace Veir

/--
  We reconcile casts in `builtin.unrealized_conversion_cast` operations for `!riscv.reg` and `i64`
  types, in the `reg -> i64 -> reg` direction. `Reg.toInt` is never poison and `Int.toReg` inverts
  it at width 64, so the round trip is the identity.
-/
def isRegToI64RoundTrip (inputType interType : TypeAttr): Bool :=
 match inputType.val, interType.val with
  | .registerType _, .integerType x => x.bitwidth = 64
  | _, _ => false

/-!
 We reconcile casts in `builtin.unrealized_conversion_cast` operations for `!llvm.ptr` and `!riscv.reg` types.
 This cast assums that the `.llvmPointerType` is bit-wide.
-/
def isRiscvRegToPtrCast (inputType interType : TypeAttr): Bool :=
 match inputType.val, interType.val with
  | .llvmPointerType _ , .registerType _ => true
  | .registerType _, .llvmPointerType _  => true
  | _, _ => false

/-- Reconciles round-trip casts of the form X->Y->X if allowed for these types by `legal X Y`.

  The parent cast is left in place: it is now dead, and DCE (run at the end of the pass) removes
  it. A `LocalRewritePattern` may only erase the matched operation. -/
def reconcilePairingCastLocal (legal : TypeAttr → TypeAttr → Bool) (ctx : WfIRContext OpCode)
    (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some input := matchCastOp op ctx.raw | return (ctx, none)
  /- Note that reconciliation matches on the second casting operation, so the input type of this op would be the intermediate type -/
  let interType := input.getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return (ctx, none)
  let some parentInput := matchCastOp op'.op ctx.raw | return (ctx, none)
  /- And the result's type coincides with the parent operation operand's type -/
  let inputType := parentInput.getType! ctx.raw
  if resultType ≠ inputType then return (ctx, none)
  /- And the reconciliation is legal -/
  if ¬ legal inputType interType then return (ctx, none)
  /- Replace the initial operation's output with the parent operation's input -/
  return (ctx, some (#[], #[parentInput]))

/-- Reconciles round-trip casts of the form !riscv.reg->iX->!riscv.reg
   using zext.b/w/h for 8/16/32-bit values, or slli+slri for other bitwidths.

  As in `reconcilePairingCastLocal`, the now-dead parent cast is left to DCE. -/
def reconcileRegIntCastLocal (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some input := matchCastOp op ctx.raw | return (ctx, none)
  /- Note that reconciliation matches on the second casting operation, so the input type of this op would be the intermediate type -/
  let interType := input.getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return (ctx, none)
  let some parentInput := matchCastOp op'.op ctx.raw | return (ctx, none)
  /- And the result's type coincides with the parent operation operand's type -/
  let inputType := parentInput.getType! ctx.raw
  if resultType ≠ inputType then return (ctx, none)
  /- And the reconciliation involves the right types -/
  if inputType ≠ RegisterType.mk then return (ctx, none)
  let .integerType ⟨ interBw ⟩ := interType.val | return (ctx, none)
  /- Replace the initial operation's output with a zero-extension of the parent's input -/
  match interBw with
  | 8 =>
      let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .zextb) #[RegisterType.mk] #[parentInput]
        #[] #[] () none
      return (ctx, some (#[newOp], #[newOp.getResult 0]))
  | 16 =>
      let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .zexth) #[RegisterType.mk] #[parentInput]
        #[] #[] () none
      return (ctx, some (#[newOp], #[newOp.getResult 0]))
  | 32 =>
      let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .zextw) #[RegisterType.mk] #[parentInput]
        #[] #[] () none
      return (ctx, some (#[newOp], #[newOp.getResult 0]))
  | bw =>
      /- `i0` has no bits to preserve: the round trip is the constant zero, which neither
         `slli`/`srli` (whose 6-bit shift amount would wrap `64 - 0` to `0`) nor any other
         two-shift sequence computes. Leave such casts alone. -/
      if bw = 0 then return (ctx, none)
      /- for bitwidths with no dedicated instruction, shift left then right -/
      if bw >= 64 then none else
      let imm := IntegerAttr.mk (64-bw) (.mk 64)
      let (ctx, shlOp) ← WfRewriter.createOp! ctx (.riscv .slli) #[RegisterType.mk] #[parentInput]
        #[] #[] ⟨imm⟩ none
      let (ctx, srlOp) ← WfRewriter.createOp! ctx (.riscv .srli) #[RegisterType.mk]
        #[shlOp.getResult 0] #[] #[] ⟨imm⟩ none
      return (ctx, some (#[shlOp, srlOp], #[srlOp.getResult 0]))

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
/-- Rewrite a function op's `function_type` to the given input/output type lists.
    `llvm.func` is canonicalized to the `.llvmFunctionType` spelling, regardless of
    which spelling the original attribute used. -/
def setFunctionType (c : WfIRContext OpCode) (funcOp : OperationPtr)
    (inputs outputs : Array Attribute) : WfIRContext OpCode :=
  let ftType : TypeAttr :=
    match funcOp.getOpType! c.raw with
    | .llvm .func => ⟨.llvmFunctionType { inputs, outputs }, by rfl⟩
    | _ => ⟨.functionType { inputs, outputs }, by rfl⟩
  match funcOp.getOpType! c.raw with
  | .func .func =>
    let props : FuncFuncProperties := funcOp.getProperties! c.raw (.func .func)
    let newEntries := props.extra.entries.map fun (k, v) =>
      if k == "function_type".toUTF8 then (k, ftType.val) else (k, v)
    let newProps : FuncFuncProperties := { props with extra := DictionaryAttr.fromArray newEntries }
    ⟨funcOp.setProperties (opCode := .func .func) c.raw newProps sorry sorry, sorry⟩
  | .llvm .func =>
    let props : LLVMFuncProperties := funcOp.getProperties! c.raw (.llvm .func)
    let newProps : LLVMFuncProperties := { props with function_type := some ftType }
    ⟨funcOp.setProperties (opCode := .llvm .func) c.raw newProps sorry sorry, sorry⟩
  | _ => c

set_option warn.sorry false in
/-- Coerce one function's `i32`/`i64` arguments and return values to `!riscv.reg`,
    inserting bridging casts and rewriting the `function_type` to match. Handles both
    `func.func` and `llvm.func`. -/
def coerceFunction (ctx : WfIRContext OpCode) (funcOp : OperationPtr) :
    ExceptT String IO (WfIRContext OpCode) := do
  -- Shadow the parameter: from here on `ctx` always names the latest version, with no
  -- separate old binding left around to second-guess.
  let mut ctx := ctx
  let some entry := FunctionOpInterface.getFirstBlock? funcOp ctx.raw | return ctx
  let returnCode := returnOpCodeFor (funcOp.getOpType! ctx.raw)
  -- Default the output types to the currently-declared ones, then flip coerced positions.
  -- This preserves non-integer results and `llvm.func`'s `void` return.
  let mut outputs : Array Attribute := (FunctionOpInterface.getResultTypes? funcOp ctx.raw).getD #[]
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
  ctx := setFunctionType ctx funcOp inputs outputs
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

def CastReconcilePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let ctx ← coerceFunctionBoundaries ctx
  let pattern := RewritePattern.GreedyRewritePattern #[
    .fromLocalRewrite (reconcilePairingCastLocal isRegToI64RoundTrip),
    .fromLocalRewrite (reconcilePairingCastLocal isRiscvRegToPtrCast),
    .fromLocalRewrite reconcileRegIntCastLocal]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying cast reconciliation"
  -- The patterns leave the (now dead) parent casts behind: `LocalRewritePattern` can only erase
  -- the matched operation. Clean them up here so the pass is self-contained.
  | some ctx =>
    match RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern #[eliminateDeadOp]) ctx with
    | none => throw "Error while applying DCE after cast reconciliation"
    | some ctx => pure ctx

public def CastReconcilePass : Pass OpCode :=
  { name := "reconcile-cast"
    description := "Reconcile round trips of casts that return to their own input type."
    run := CastReconcilePass.impl }
