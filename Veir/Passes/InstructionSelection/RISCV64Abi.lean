module

public import Veir.Pass
import Veir.IR.SymbolRef
import Veir.Passes.FunctionBoundaryCoercion.Coercion
import Veir.Passes.InstructionSelection.Common
import Veir.Passes.Matching
import Veir.PatternRewriter.Basic

namespace Veir

/-!
  # Lowering to the RISC-V calling convention

  1. LLVM function boundaries are coerced to `!riscv.reg`
     (`coerceFunctionBoundaries .riscvReg`).
  2. Every `llvm.return` of a function whose operands are now registers
     becomes a `riscv_cf.return`.
  3. Every `llvm.call` whose arguments and results are passed in a single
     integer register becomes a `riscv_cf.call`, with its operands cast to registers in
     front of it and its results cast back to their original types after it.
-/

/-- ABI requirements and call semantics that we do not lower yet. -/
private def isUnsupportedAbiAttr (entry : ByteArray × Attribute) : Bool :=
  let (name, attr) := entry
  if name == "CConv".toUTF8 then
    match attr with
    | .cconvAttr cc => cc.value.trimAscii.toString != "ccc"
    | _ => true
  -- MIR must record exposesReturnsTwice before these calls can be lowered safely.
  else if name == "returns_twice".toUTF8 then true
  else if name == "arg_attrs".toUTF8 || name == "res_attrs".toUTF8 then
    match attr with
    | .arrayAttr attrs => attrs.value.any fun attr =>
      match attr with
      | .dictionaryAttr dict => dict.entries.any fun (name, _) =>
        name == "llvm.byval".toUTF8 || name == "llvm.inalloca".toUTF8 ||
          name == "llvm.nest".toUTF8 ||
          name == "llvm.signext".toUTF8 || name == "llvm.zeroext".toUTF8
      | _ => false
    | _ => false
  else false

/-- Required tail calls and bundles (even with zero operands) also need separate support. -/
private def isUnsupportedCallAttr (entry : ByteArray × Attribute) : Bool :=
  let (name, attr) := entry
  isUnsupportedAbiAttr entry ||
    if name == "TailCallKind".toUTF8 then
      match attr with
      | .tailCallKindAttr kind => kind.value.trimAscii.toString == "musttail"
      | _ => true
    else if name == "op_bundle_sizes".toUTF8 then
      match attr with
      | .denseArrayAttr sizes => !sizes.values.isEmpty
      | _ => true
    else if name == "op_bundle_tags".toUTF8 then
      match attr with
      | .arrayAttr tags => !tags.value.isEmpty
      | _ => true
    else false

/-- Check properties and discardable attributes with the same predicate. -/
private def hasUnsupportedAttrs (properties attrs : Array (ByteArray × Attribute))
    (unsupported : ByteArray × Attribute → Bool) : Bool :=
  properties.any unsupported || attrs.any unsupported

private def supportsFunctionAbi (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  let opType := op.getOpType! ctx
  let properties := Properties.toAttrDict opType (op.getProperties! ctx opType)
  !hasUnsupportedAttrs properties.toArray (op.get! ctx).attrs.entries isUnsupportedAbiAttr

/-- Resolve a flat callee name in the nearest enclosing module. Do not look through
    nested modules: a same-named function there belongs to a different symbol scope. -/
private partial def lookupCallee? (ctx : IRContext OpCode) (op : OperationPtr)
    (name : ByteArray) : Option OperationPtr := do
  let parent ← op.getParentOp! ctx
  if parent.getOpType! ctx != .builtin .module then
    return ← lookupCallee? ctx parent name
  let body := parent.getRegion! ctx 0
  let block ← (body.get! ctx).firstBlock
  let mut candidate := (block.get! ctx).firstOp
  while let some target := candidate do
    if let some func := FunctionOp.cast? target ctx then
      if func.getSymName.value == name then return target
    candidate := (target.get! ctx).next
  none

/-- Whether a value of type `t` is passed in a single integer register. -/
def isRegPassed (t : TypeAttr) : Bool :=
  (BoundaryCoercion.riscvReg.target t).isSome

/--
  `reg` holds a value of type `type` zero-extended to 64 bits. If `type` is `i32`,
  sign-extend it instead, as the psABI requires.
-/
def sextIfI32 (ctx : WfIRContext OpCode) (type : TypeAttr) (reg : ValuePtr)
    : Option (WfIRContext OpCode × Array OperationPtr × ValuePtr) := do
  let .integerType t := type.val | return (ctx, #[], reg)
  if t.bitwidth ≠ 32 then return (ctx, #[], reg)
  let (ctx, sext) ← WfRewriter.createOp! ctx Riscv.sextw #[RegisterType.mk] #[reg]
    #[] #[] () none
  return (ctx, #[sext], sext.getResult 0)

/--
  Replace `op` by a `riscv_cf.return` if it returns registers from a function. The
  boundary coercion casts each coerced return value to a register; an `i32` one is
  sign-extended after its cast.
-/
def lowerReturn : LocalRewritePattern OpCode := fun ctx op => do
  let some parent := op.getParentOp! ctx.raw | return (ctx, none)
  if parent.getOpType! ctx.raw != .llvm .func || !supportsFunctionAbi ctx.raw parent then
    return (ctx, none)
  let operands := op.getOperands! ctx.raw
  if !operands.all (fun v => (v.getType! ctx.raw).isa RegisterType) then return (ctx, none)
  let (ctx, newOps, regs) ← operands.foldlM (init := (ctx, #[], #[])) fun (ctx, newOps, regs) v => do
    let (ctx, sextOps, reg) ← match v.definingOp?.bind (matchCastOp · ctx.raw) with
      | some input => sextIfI32 ctx (input.getType! ctx.raw) v
      | none => pure (ctx, #[], v)
    return (ctx, newOps ++ sextOps, regs.push reg)
  let (ctx, ret) ← WfRewriter.createOp! ctx Riscv_Cf.return #[] regs #[] #[] () none
  return (ctx, some (newOps.push ret, #[]))

/--
  Replace the call `op` to `callee` by a `riscv_cf.call` if all of its arguments and
  results are passed in a single integer register and there are at most eight
  arguments. An indirect `llvm.call`'s first operand is its target pointer, which
  `riscv_cf.call` also takes first and does not count toward the argument limit.
  Direct calls must also satisfy the ABI attributes on the callee, even when
  those attributes are not repeated on the call.
-/
def lowerCall (callee : Option FlatSymbolRefAttr) (extra : DictionaryAttr) :
    LocalRewritePattern OpCode := fun ctx op => do
  if hasUnsupportedAttrs extra.entries (op.get! ctx.raw).attrs.entries isUnsupportedCallAttr then
    return (ctx, none)
  if let some callee := callee then
    let some name := callee.getName? | return (ctx, none)
    if let some target := lookupCallee? ctx.raw op name then
      if !supportsFunctionAbi ctx.raw target then return (ctx, none)
  let operands := op.getOperands! ctx.raw
  -- Stack arguments are not lowered yet; an indirect target is not an argument.
  let numArgs := operands.size - (if callee.isSome then 0 else 1)
  if numArgs > 8 then return (ctx, none)
  let resultTypes := op.getResultTypes! ctx.raw
  if !operands.all (fun v => isRegPassed (v.getType! ctx.raw)) || !resultTypes.all isRegPassed then
    return (ctx, none)
  let (ctx, newOps, regs) ← operands.foldlM (init := (ctx, #[], #[])) fun (ctx, newOps, regs) v => do
    let (ctx, cast) ← castToRegLocal ctx v
    let (ctx, sextOps, reg) ← sextIfI32 ctx (v.getType! ctx.raw) (cast.getResult 0)
    return (ctx, newOps.push cast ++ sextOps, regs.push reg)
  let (ctx, call) ← WfRewriter.createOp! ctx Riscv_Cf.call
    (resultTypes.map fun _ => RegisterType.mk) regs #[] #[] ({ callee } : RISCVCallProperties) none
  let newOps := newOps.push call
  -- LLVM calls have at most one result.
  if resultTypes.isEmpty then return (ctx, some (newOps, #[]))
  let (ctx, cast) ← replaceWithRegLocal ctx op (call.getResult 0)
  return (ctx, some (newOps.push cast, #[cast.getResult 0]))

/-- Lower `op` if it is an LLVM return or call. -/
def lowerOp : LocalRewritePattern OpCode := fun ctx op =>
  match op.getOpType! ctx.raw with
  | .llvm .return => lowerReturn ctx op
  | .llvm .call =>
    let props : LLVMCallProperties := op.getProperties! ctx.raw (OpCode.llvm .call)
    lowerCall props.callee props.extra ctx op
  | _ => pure (ctx, none)

/-! # Pass implementation -/

def IselAbiRISCV64.impl (ctx : WfIRContext OpCode) (_op : OperationPtr)
    (_ : _op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let ctx ← coerceFunctionBoundaries .riscvReg ctx fun ctx op =>
    op.getOpType! ctx == .llvm .func && supportsFunctionAbi ctx op
  -- The rewrite driver inserts the new operations, replaces results, and removes dead casts.
  match RewritePattern.applyInContext (.fromLocalRewrite lowerOp) ctx with
  | none => throw "Error while applying isel-abi-riscv64"
  | some ctx => pure ctx

public def IselAbiRISCV64 : Pass OpCode :=
  { name := "isel-abi-riscv64"
    description :=
      "Lower LLVM function boundaries, returns and calls to the RISC-V calling convention."
    run := fun _ => IselAbiRISCV64.impl }
