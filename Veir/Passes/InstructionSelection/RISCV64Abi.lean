module

public import Veir.Pass
import Veir.Interfaces.CallInterfaces
import Veir.Passes.FunctionBoundaryCoercion.Coercion
import Veir.Passes.InstructionSelection.Common
import Veir.Passes.Matching
import Veir.PatternRewriter.Basic

namespace Veir

/-!
  # Lowering to the RISC-V calling convention

  This pass runs right after `llvm-to-gmir`, like LLVM's `RISCVCallLowering`. A register
  holds an `i64`, so narrower values are copied into it with a gMIR extension and out of it
  with a `g_trunc`. These are legalization artifacts: the legalizer folds a `g_trunc` into
  the `g_anyext` or `g_trunc` that uses it, but not yet into a `g_sext` or `g_zext`.

  1. LLVM function boundaries are coerced to `!riscv.reg`
     (`coerceFunctionBoundaries .riscvReg`), and the arguments are copied out of
     their registers.
  2. Every `llvm.return` of a function whose operands are now registers
     becomes a `riscv_cf.return`.
  3. Every `llvm.call` whose arguments and results are passed in a single
     integer register becomes a `riscv_cf.call`, with its operands copied to registers in
     front of it and its results copied out of registers after it.
-/

/-- ABI requirements and call semantics that we do not lower yet. -/
private def isUnsupportedAbiAttr (entry : ByteArray × Attribute) : Bool :=
  let (name, attr) := entry
  if name == "CConv".toUTF8 then
    match attr with
    | .cconvAttr cc =>
      let cc := cc.value.trimAscii.toString
      cc != "ccc" && cc != "fastcc"
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

/-- The properties and discardable attributes of `op`, where its `arg_attrs` and `res_attrs` live. -/
private def abiAttrEntries (ctx : IRContext OpCode) (op : OperationPtr) :
    Array (ByteArray × Attribute) :=
  let opType := op.getOpType! ctx
  (Properties.toAttrDict opType (op.getProperties! ctx opType)).toArray ++ (op.getAttributes! ctx).entries

/-- Whether a value of type `t` is passed in a single integer register. -/
def isRegPassed (t : TypeAttr) : Bool :=
  (BoundaryCoercion.riscvReg.target t).isSome

/--
  Whether every argument and result of the function `op` is passed in a single integer
  register, or already is one. Otherwise its boundary would only be partly coerced, so
  the whole function is left unlowered. A variadic function is left unlowered too: its
  variadic arguments are not modeled.
-/
private def hasRegBoundary (ctx : IRContext OpCode) (op : OperationPtr) : Bool := Id.run do
  let some funcOp := FunctionOp.of? op ctx | return false
  if funcOp.getFunctionType.isVarArg then return false
  let regPassed (t : Attribute) : Bool :=
    (t matches .registerType _) || (if h : t.isType then isRegPassed (t.asType h) else false)
  return funcOp.getArgumentTypes.all regPassed &&
    funcOp.getResultTypes.all fun t => (t matches .llvmVoidType _) || regPassed t

private def supportsFunctionAbi (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  !(abiAttrEntries ctx op).any isUnsupportedAbiAttr && hasRegBoundary ctx op

/--
  Extend `v` to `i64` as `ext` requests, with the gMIR extension of LLVM's
  `extendOpFromFlags`. An `i32` is sign-extended, as the psABI requires, unless
  it is `zeroext`.
-/
def extendForAbi (ctx : WfIRContext OpCode) (ext : AbiExt) (v : ValuePtr)
    : Option (WfIRContext OpCode × Array OperationPtr × ValuePtr) := do
  let .integerType t := (v.getType! ctx.raw).val | return (ctx, #[], v)
  if 64 ≤ t.bitwidth then return (ctx, #[], v)
  let extOp := match ext, t.bitwidth with
    | .sext, _ | .none, 32 => GMIR.g_sext
    | .zext, _ => GMIR.g_zext
    | .none, _ => GMIR.g_anyext
  let (ctx, extend) ← WfRewriter.createOp! ctx extOp #[IntegerType.signless 64] #[v] #[] #[]
    default none
  return (ctx, #[extend], extend.getResult 0)

/-- Copy `v` to a register, extended as `extendForAbi` describes, like LLVM's `buildCopyToRegs`. -/
def copyToReg (ctx : WfIRContext OpCode) (ext : AbiExt) (v : ValuePtr)
    : Option (WfIRContext OpCode × Array OperationPtr × ValuePtr) := do
  let (ctx, extOps, wide) ← extendForAbi ctx ext v
  let (ctx, cast) ← castToRegLocal ctx wide
  return (ctx, extOps.push cast, cast.getResult 0)

/--
  Copy the register `reg` out to a value of type `type`, like LLVM's `buildCopyFromRegs`.
  A narrower integer is a `g_trunc` of the register's `i64`.
-/
def copyFromReg (ctx : WfIRContext OpCode) (type : TypeAttr) (reg : ValuePtr)
    : Option (WfIRContext OpCode × Array OperationPtr × ValuePtr) := do
  let narrow := match type.val with
    | .integerType t => t.bitwidth < 64
    | _ => false
  let wideType : TypeAttr := if narrow then IntegerType.signless 64 else type
  let (ctx, cast) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast
    #[wideType] #[reg] #[] #[] () none
  if !narrow then return (ctx, #[cast], cast.getResult 0)
  let (ctx, trunc) ← WfRewriter.createOp! ctx GMIR.g_trunc #[type] #[cast.getResult 0] #[] #[]
    default none
  return (ctx, #[cast, trunc], trunc.getResult 0)

/--
  Copy a narrow argument out of its register, like LLVM's `RISCVCallLowering::lowerFormalArguments`.
  `op` is the cast of a register argument that the boundary coercion inserts at the entry.
  Arguments of other blocks are left alone.
-/
def lowerFormalArgument : LocalRewritePattern OpCode := fun ctx op => do
  let some reg := matchCastOp op ctx.raw | return (ctx, none)
  let .blockArgument arg := reg | return (ctx, none)
  if !(reg.getType! ctx.raw).isa RegisterType then return (ctx, none)
  let some region := arg.block.getParent! ctx.raw | return (ctx, none)
  if region.getFirstBlock! ctx.raw != some arg.block then return (ctx, none)
  let some func := region.getParent! ctx.raw | return (ctx, none)
  if func.getOpType! ctx.raw != .llvm .func || !supportsFunctionAbi ctx.raw func then
    return (ctx, none)
  let type := (op.getResult 0).getType! ctx.raw
  -- A full-width argument is already copied by the cast.
  let .integerType t := type.val | return (ctx, none)
  if 64 ≤ t.bitwidth then return (ctx, none)
  let (ctx, ops, value) ← copyFromReg ctx type reg
  return (ctx, some (ops, #[value]))

/--
  Replace `op` by a `riscv_cf.return` if it returns registers from a function. Each
  value that the boundary coercion casts to a register is copied to it as `copyToReg` describes.
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
      | some input => copyToReg ctx (abiExtOf entries "res_attrs" i) input
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
  if hasUnsupportedAttrs extra.entries (op.getAttributes! ctx.raw).entries isUnsupportedCallAttr then
    return (ctx, none)
  let mut calleeEntries := #[]
  if callee.isSome then
    let some callOp := CallOp.of? op ctx.raw | none
    let some target := callOp.resolveCallable? | return (ctx, none)
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
  let callEntries := extra.entries ++ (op.getAttributes! ctx.raw).entries
  let argExt (i : Nat) : AbiExt :=
    if i < numTargets then .none else
    match abiExtOf callEntries "arg_attrs" (i - numTargets) with
    | .none => abiExtOf calleeEntries "arg_attrs" (i - numTargets)
    | ext => ext
  let (ctx, newOps, regs) ← operands.zipIdx.foldlM (init := (ctx, #[], #[]))
      fun (ctx, newOps, regs) (v, i) => do
    let (ctx, copyOps, reg) ← copyToReg ctx (argExt i) v
    return (ctx, newOps ++ copyOps, regs.push reg)
  let (ctx, call) ← WfRewriter.createOp! ctx Riscv_Cf.call
    (resultTypes.map fun _ => RegisterType.mk) regs #[] #[] ({ callee } : RISCVCallProperties) none
  let newOps := newOps.push call
  -- LLVM calls have at most one result.
  if resultTypes.isEmpty then return (ctx, some (newOps, #[]))
  let (ctx, copyOps, value) ← copyFromReg ctx resultTypes[0]! (call.getResult 0)
  return (ctx, some (newOps ++ copyOps, #[value]))

/-- Lower `op` if it is an argument cast, or an LLVM return or call. -/
def lowerOp : LocalRewritePattern OpCode := fun ctx op =>
  match op.getOpType! ctx.raw with
  | .builtin .unrealized_conversion_cast => lowerFormalArgument ctx op
  | .llvm .return => lowerReturn ctx op
  | .llvm .call =>
    let props : LLVMCallProperties := op.getProperties! ctx.raw (OpCode.llvm .call)
    lowerCall props.callee props.extra ctx op
  | _ => pure (ctx, none)

/-! # Pass implementation -/

def CallLoweringRISCV64.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let ctx ← coerceFunctionBoundaries .riscvReg ctx fun ctx op =>
    op.getOpType! ctx == .llvm .func && supportsFunctionAbi ctx op
  -- The rewrite driver inserts the new operations, replaces results, and removes dead casts.
  match RewritePattern.applyToFunctions (.fromLocalRewrite lowerOp) ctx op with
  | none => throw "Error while applying call-lowering-riscv64"
  | some ctx => pure ctx

public def CallLoweringRISCV64 : Pass OpCode :=
  { name := "call-lowering-riscv64"
    description :=
      "Lower LLVM function boundaries, returns and calls to the RISC-V calling convention."
    run := fun _ => CallLoweringRISCV64.impl }
