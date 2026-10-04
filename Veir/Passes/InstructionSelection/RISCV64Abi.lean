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
  else if name == "passthrough".toUTF8 then
    match attr with
    | .arrayAttr attrs => attrs.value.any fun
      | .stringAttr name => name.value == "returns_twice".toUTF8
      -- Passthrough entries may also be [name, value] pairs.
      | .arrayAttr pair =>
        match (pair.value[0]? : Option Attribute) with
        | some (.stringAttr name) => name.value == "returns_twice".toUTF8
        | _ => false
      | _ => false
    | _ => false
  else if name == "arg_attrs".toUTF8 || name == "res_attrs".toUTF8 then
    match attr with
    | .arrayAttr attrs => attrs.value.any fun attr =>
      match attr with
      | .dictionaryAttr dict => dict.entries.any fun (name, _) =>
        name == "llvm.byval".toUTF8 || name == "llvm.inalloca".toUTF8 ||
          name == "llvm.nest".toUTF8
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

/-- How a boundary value is extended to a full register (`llvm.signext`/`llvm.zeroext`). -/
inductive AbiExt where
  | none
  | sext
  | zext
deriving DecidableEq

/-- The extension requested by entry `i` of the `arg_attrs` or `res_attrs` (`key`) array. -/
def abiExtOf (entries : Array (ByteArray × Attribute)) (key : String) (i : Nat) : AbiExt := Id.run do
  let some (_, .arrayAttr attrs) := entries.find? (·.1 == key.toUTF8) | return .none
  let some (.dictionaryAttr dict) := attrs.value[i]? | return .none
  if dict.entries.any (·.1 == "llvm.signext".toUTF8) then return .sext
  if dict.entries.any (·.1 == "llvm.zeroext".toUTF8) then return .zext
  return .none

/--
  `zeroext i32` is not lowered: the psABI sign-extends every 32-bit value, while LLVM
  zero-extends it. Clang never emits it for RV64.
-/
def isUnsupportedExt (type : Attribute) (ext : AbiExt) : Bool :=
  match type with
  | .integerType t => ext == .zext && t.bitwidth == 32
  | _ => false

/-- The properties and discardable attributes of `op`, where its `arg_attrs` and `res_attrs` live. -/
private def abiAttrEntries (ctx : IRContext OpCode) (op : OperationPtr) :
    Array (ByteArray × Attribute) :=
  let opType := op.getOpType! ctx
  (Properties.toAttrDict opType (op.getProperties! ctx opType)).toArray ++ (op.get! ctx).attrs.entries

private def supportsFunctionAbi (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  let entries := abiAttrEntries ctx op
  match FunctionOp.cast? op ctx with
  | none => false
  | some funcOp =>
    !entries.any isUnsupportedAbiAttr &&
      !(funcOp.getArgumentTypes.zipIdx.any fun (t, i) => isUnsupportedExt t (abiExtOf entries "arg_attrs" i)) &&
      !(funcOp.getResultTypes.zipIdx.any fun (t, i) => isUnsupportedExt t (abiExtOf entries "res_attrs" i))

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
  Extend `reg`, which holds a value of type `type` in its low bits, to the full
  register as `ext` requests. An `i32` is always sign-extended, as the psABI requires.
  The sequences match `llc -mtriple=riscv64 -mattr=+zbb`.
-/
def extendForAbi (ctx : WfIRContext OpCode) (ext : AbiExt) (type : TypeAttr) (reg : ValuePtr)
    : Option (WfIRContext OpCode × Array OperationPtr × ValuePtr) := do
  let .integerType t := type.val | return (ctx, #[], reg)
  match ext, t.bitwidth with
  | .sext, 1 =>
    let (ctx, shl) ← createRISCVImmLocal ctx .slli rfl #[reg] 63
    let (ctx, sra) ← createRISCVImmLocal ctx .srai rfl #[shl.getResult 0] 63
    return (ctx, #[shl, sra], sra.getResult 0)
  | .zext, 1 =>
    let (ctx, andOp) ← createRISCVImmLocal ctx .andi rfl #[reg] 1
    return (ctx, #[andOp], andOp.getResult 0)
  | .sext, 8 => extendWith ctx .sextb rfl reg
  | .zext, 8 => extendWith ctx .zextb rfl reg
  | .sext, 16 => extendWith ctx .sexth rfl reg
  | .zext, 16 => extendWith ctx .zexth rfl reg
  | _, 32 => extendWith ctx .sextw rfl reg
  | _, _ => return (ctx, #[], reg)
where
  extendWith (ctx : WfIRContext OpCode) (dst : Riscv) (h : Riscv.propertiesOf dst = Unit)
      (reg : ValuePtr) : Option (WfIRContext OpCode × Array OperationPtr × ValuePtr) := do
    let (ctx, extOp) ← createRISCVUnitLocal ctx dst h #[reg]
    return (ctx, #[extOp], extOp.getResult 0)

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
  let entries := abiAttrEntries ctx.raw parent
  let (ctx, newOps, regs) ← operands.zipIdx.foldlM (init := (ctx, #[], #[]))
      fun (ctx, newOps, regs) (v, i) => do
    let (ctx, extOps, reg) ← match v.definingOp?.bind (matchCastOp · ctx.raw) with
      | some input => extendForAbi ctx (abiExtOf entries "res_attrs" i) (input.getType! ctx.raw) v
      | none => pure (ctx, #[], v)
    return (ctx, newOps ++ extOps, regs.push reg)
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
  let mut calleeEntries := #[]
  if let some callee := callee then
    let some name := callee.getName? | return (ctx, none)
    if let some target := lookupCallee? ctx.raw op name then
      if !supportsFunctionAbi ctx.raw target then return (ctx, none)
      calleeEntries := abiAttrEntries ctx.raw target
  let operands := op.getOperands! ctx.raw
  -- Stack arguments are not lowered yet; an indirect target is not an argument.
  let numTargets := if callee.isSome then 0 else 1
  if operands.size - numTargets > 8 then return (ctx, none)
  let resultTypes := op.getResultTypes! ctx.raw
  if !operands.all (fun v => isRegPassed (v.getType! ctx.raw)) || !resultTypes.all isRegPassed then
    return (ctx, none)
  -- The call site's extension attribute, or else the callee's, like `CallBase::paramHasAttr`.
  let callEntries := extra.entries ++ (op.get! ctx.raw).attrs.entries
  let argExt (i : Nat) : AbiExt :=
    if i < numTargets then .none else
    match abiExtOf callEntries "arg_attrs" (i - numTargets) with
    | .none => abiExtOf calleeEntries "arg_attrs" (i - numTargets)
    | ext => ext
  if operands.zipIdx.any (fun (v, i) => isUnsupportedExt (v.getType! ctx.raw).val (argExt i)) ||
      resultTypes.any (isUnsupportedExt ·.val (abiExtOf callEntries "res_attrs" 0)) then
    return (ctx, none)
  let (ctx, newOps, regs) ← operands.zipIdx.foldlM (init := (ctx, #[], #[]))
      fun (ctx, newOps, regs) (v, i) => do
    let (ctx, cast) ← castToRegLocal ctx v
    let (ctx, extOps, reg) ← extendForAbi ctx (argExt i) (v.getType! ctx.raw) (cast.getResult 0)
    return (ctx, newOps.push cast ++ extOps, regs.push reg)
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
