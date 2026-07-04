import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.DCE.dce
import Veir.Rewriter.WfRewriter
import Veir.Properties

namespace Veir

/-!
  We reconcile casts in `builtin.unrealized_conversion_cast` operations for `!riscv.reg` and `i64` types.
-/
def isRiscvRegToI64Cast (inputType interType : TypeAttr): Bool :=
 match inputType.val, interType.val with
  | .registerType _, .integerType x => x.bitwidth = 64
  | .integerType x, .registerType _ => x.bitwidth = 64
  | _, _ => false

/-!
    We reconcile casts in `builtin.unrealized_conversion_cast` operations for `!riscv.reg` and `i32` types, however only for the `i32 -> reg -> i32` direction.
-/
def isRiscvRegToI32Cast (inputType interType : TypeAttr): Bool :=
 match inputType.val, interType.val with
  | .integerType x, .registerType _ => x.bitwidth = 32
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

/-!
  We reconcile casts in `builtin.unrealized_conversion_cast` operations for `iX` and `iY` types,
  of the form:
  ```
  %x = "builtin.unrealized_conversion_cast"(%s) : (iX) -> iY
  %y = "builtin.unrealized_conversion_cast"(%x) : (iY) -> iX
  ```
  where `X ≤ Y`, to ensure no information is loss and correctness is preserved.
-/
def isPreservingIntegerTypeRoundTrip (inputType interType : TypeAttr) : Bool :=
  match inputType.val, interType.val with
  | .integerType x, .integerType y => x.bitwidth ≤ y.bitwidth
  | _, _ => false

/- Reconciles round-trip casts of the form X->Y->X if allowed for these types by `legal X Y` -/
set_option warn.sorry false in
def reconcilePairingCast (legal : TypeAttr → TypeAttr → Bool) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some cast := matchCastOp op rewriter.ctx.raw | return rewriter
  let input := op.getOperand! rewriter.ctx.raw 0
  /- Note that reconciliation matches on the second casting operation, so the input type of this op would be the intermediate type -/
  let interType := input.getType! rewriter.ctx.raw
  let resultType := ((op.getResult 0).get! rewriter.ctx.raw).type
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return rewriter
  let some cast := matchCastOp op'.op rewriter.ctx.raw | return rewriter
  let parentInput := (op'.op.getOperand! rewriter.ctx.raw 0)
  /- And the result's type coincides with the parent operation operand's type -/
  let inputType := parentInput.getType! rewriter.ctx.raw
  if resultType ≠ inputType then return rewriter
  /- And the reconciliation is legal -/
  if ¬ legal inputType interType then return rewriter
  /- Replace the initial operation's output with the parent operations input -/
  let rewriter := rewriter.replaceValue (op.getResult 0) parentInput sorry sorry sorry
  /- Erase the redundant cast operation -/
  let rewriter ← rewriter.eraseOp op sorry sorry sorry
  /- If unused and side-effect-free, erase the parent cast operation as well.
    These need to be erased in this order, otherwise the parent operation will always be used. -/
  if ¬ op'.op.hasUses! rewriter.ctx.raw && ¬ op'.op.hasSideEffects rewriter.ctx.raw then
    rewriter.eraseOp op'.op sorry sorry sorry
  else
    return rewriter

set_option warn.sorry false in
def reconcileIdentityCast (rewriter : PatternRewriter OpCode) (op : OperationPtr)
  (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some cast := matchCastOp op rewriter.ctx.raw | return rewriter
  /- get the input and output types -/
  let input := op.getOperand! rewriter.ctx.raw 0
  let inputType := input.getType! rewriter.ctx.raw
  let resultType := ((op.getResult 0).get! rewriter.ctx.raw).type
  if inputType ≠ resultType then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) input sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ## Coercing function boundaries to `!riscv.reg`

  Before removing round-trip casts, we rewrite each `func.func` and
  `llvm.func`'s i32- and i64- and pointer-typed arguments and return
  values to `!riscv.reg`, inserting `unrealized_conversion_cast`s to
  bridge to/from the original integer types. Instruction selection
  already casts every use of a function argument (and every return
  operand) through a register, so this coercion turns those into `reg
  -> iX -> reg` round-trips that the reconciliation patterns above
  then collapse. The function's `function_type` attribute is rewritten
  to match so the verifier's return-type check still holds.

  This assumes instruction selection has already run: it is the
  responsibility of whoever invokes this pass to have lowered the
  function body first, so its boundary casts have something to
  reconcile with.
-/

/-- Whether a boundary value of this type should be coerced to `!riscv.reg`. The coercible
    types are the register-width ones passed/returned in registers by the RISC-V calling
    convention: `i64`, `i32`, and `!llvm.ptr`. (`i32`'s `reg` round-trip truncates rather
    than being the identity — see the section comment above.) -/
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
  let mut c := ctx
  -- The function body, if any, is its single region. Declarations have no blocks.
  if funcOp.getNumRegions! c.raw = 0 then return c
  let region := funcOp.getRegion! c.raw 0
  let some entry := (region.get! c.raw).firstBlock | return c
  let returnCode := returnOpCodeFor (funcOp.getOpType! c.raw)
  -- Default the output types to the currently-declared ones, then flip coerced positions.
  -- This preserves non-integer results and `llvm.func`'s `void` return.
  let declaredFt := (readFunctionType? c.raw funcOp).getD { inputs := #[], outputs := #[] }
  let mut outputs : Array Attribute := declaredFt.outputs
  -- (1) Coerce entry-block arguments (the function parameters). This mirrors the
  --     block-argument coercion in `isel-br-riscv64`, which skips entry blocks.
  let mut inputs : Array Attribute := #[]
  for i in List.range (entry.getNumArguments! c.raw) do
    let bap : BlockArgumentPtr := { block := entry, index := i }
    let origType := (ValuePtr.blockArgument bap).getType! c.raw
    if isRegCoercibleType origType then
      c := WfRewriter.setType c bap RegisterType.mk sorry
      let ip := InsertPoint.atStart entry c.raw sorry
      let some (c', cast) := WfRewriter.createOp c
        (.builtin .unrealized_conversion_cast) #[origType] #[] #[] #[] default (some ip)
        sorry sorry sorry sorry | return c
      let c' := WfRewriter.replaceValue c' bap (cast.getResult 0) sorry sorry sorry
      c := WfRewriter.pushOperand c' cast bap sorry sorry
      inputs := inputs.push (.registerType ⟨none⟩)
    else
      inputs := inputs.push origType.val
  -- (2) Coerce the operands of every return terminator in this function.
  let returnOps := c.raw.operations.keys.filter fun o =>
    o.getOpType! c.raw == returnCode &&
      o.getParentOp! c.raw == some funcOp
  for retOp in returnOps do
    for j in List.range (retOp.getNumOperands! c.raw) do
      let opVal := retOp.getOperand! c.raw j
      let opType := opVal.getType! c.raw
      if isRegCoercibleType opType then
        let some (c', cast) := WfRewriter.createOp c
          (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[opVal] #[] #[] default
          (some (InsertPoint.before retOp)) sorry sorry sorry sorry | return c
        c := WfRewriter.replaceOperand c' ⟨retOp, j⟩ (cast.getResult 0) sorry sorry
        -- The `j`-th operand maps to the `j`-th declared result (for non-void returns).
        if j < outputs.size then
          outputs := outputs.set! j (.registerType ⟨none⟩)
  -- (3) Rewrite the function_type to reflect the coerced boundary types.
  c := setFunctionType c funcOp inputs outputs
  return c

/-- Coerce every `func.func` and `llvm.func` in the module (see `coerceFunction`). -/
def coerceFunctionBoundaries (ctx : WfIRContext OpCode) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut c := ctx
  let funcOps := ctx.raw.operations.keys.filter fun o =>
    match o.getOpType! ctx.raw with
    | .func .func | .llvm .func => true
    | _ => false
  for funcOp in funcOps do
    c ← coerceFunction c funcOp
  return c

def CastReconcilePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  -- First coerce function argument/return boundaries to registers, turning the
  -- boundary casts into round-trips that the reconciliation patterns below remove.
  let ctx ← coerceFunctionBoundaries ctx
  let pattern := RewritePattern.GreedyRewritePattern #[reconcilePairingCast isRiscvRegToI64Cast, reconcilePairingCast isRiscvRegToI32Cast, reconcilePairingCast isRiscvRegToPtrCast, reconcilePairingCast isPreservingIntegerTypeRoundTrip, reconcileIdentityCast]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying cast reconciliation"
  | some ctx => pure ctx

public def CastReconcilePass : Pass OpCode :=
  { name := "reconcile-cast"
    description := "Reconcile casts where the input and output types are the same."
    run := CastReconcilePass.impl }
