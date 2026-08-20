module

public import Veir.Verifier.Lemmas
public import Veir.GlobalOpInfo
public import Veir.Interfaces.FunctionInterfaces
public import Veir.IRNesting
public import Veir.Interfaces.RegionKindInterfaces

import all Veir.Verifier.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.ModArith.OpInfo

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
  Verify operation/block control-flow position rules: a terminator
  only ever appears as the last operation of its block, and any
  operation carrying block successors must also be the last operation
  of its block. The second rule is MLIR's, from
  `verifyOnEntrance(Block &)` in `mlir/lib/IR/Verifier.cpp`.
-/
def OperationPtr.verifyTerminatorPosition (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let operation := op.get ctx.raw opIn
  if operation.opType.isTerminator && operation.next.isSome then
    throw "Expected a terminator to be the last operation of its block"
  if op.getNumSuccessors ctx.raw opIn ≠ 0 && operation.next.isSome then
    throw "operation with block successors must terminate its parent block"

/--
Find the region that establishes the nearest `IsolatedFromAbove` scope around
`region`. The returned region is one of the isolated operation's direct
regions; different regions of the same isolated operation are separate scopes.
-/
private partial def RegionPtr.nearestIsolatedScope?
    (region : RegionPtr) (ctx : WfIRContext OpCode) : Option RegionPtr := do
  let parentOp ← (region.get! ctx.raw).parent
  if (parentOp.getOpType! ctx.raw).isIsolatedFromAbove then
    return region
  let parentRegion ← parentOp.getParentRegion! ctx.raw
  parentRegion.nearestIsolatedScope? ctx

/--
Verify MLIR's `IsolatedFromAbove` rule for one operation's operands. A use in
an isolated operation's region may only reference a value defined in that same
region or one of its nested regions. Looking for the nearest isolated scope
also mirrors MLIR's behavior of checking nested isolated operations
independently.
-/
def OperationPtr.verifyOperandIsolation
    (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  if op.getNumOperands ctx.raw opIn == 0 then return
  let some useRegion := op.getParentRegion! ctx.raw | return
  let escaping := (op.getOperands ctx.raw opIn).filter
    (·.getParentRegion! ctx.raw != some useRegion)
  if escaping.isEmpty then return
  let some isolatedScope := useRegion.nearestIsolatedScope? ctx | return
  for value in escaping do
    let some defRegion := value.getParentRegion! ctx.raw
      | throw "operand is unlinked from any region"
    if !isolatedScope.isAncestorOf defRegion ctx then
      throw "operand uses a value defined outside the isolated region that encloses its use"

/--
  Whether a block is exempt from the requirement that it end in a terminator,
  mirroring `mayBeValidWithoutTerminator` in `mlir/lib/IR/Verifier.cpp`.
-/
def BlockPtr.mayBeValidWithoutTerminator (block : BlockPtr) (ctx : WfIRContext OpCode)
    (blockIn : block.InBounds ctx.raw) : Bool :=
  match (block.get ctx.raw blockIn).parent with
  | none => true
  | some region =>
    (region.get! ctx.raw).firstBlock = some block &&
    (block.get ctx.raw blockIn).next.isNone &&
    match (region.get! ctx.raw).parent with
    | none => true
    | some _ => region.hasNoTerminator ctx

/--
  Check that a block is non-empty and ends in an operation that might be a
  terminator, unless the block may be valid without one. Mirrors the terminator
  half of `verifyOnEntrance`/`verifyOnExit` in `mlir/lib/IR/Verifier.cpp`.
-/
def BlockPtr.verifyTerminator (block : BlockPtr) (ctx : WfIRContext OpCode)
    (blockIn : block.InBounds ctx.raw) : Except String PUnit := do
  if block.mayBeValidWithoutTerminator ctx blockIn then
    return
  let b := block.get ctx.raw blockIn
  let named (msg : String) : String :=
    match b.parent with
    | some region =>
      match (region.get! ctx.raw).parent with
      | some parentOp => s!"{String.fromUTF8! (parentOp.getOpType! ctx.raw).name}: {msg}"
      | none => msg
    | none => msg
  match b.lastOp with
  | none => throw (named "Expected the block to end in a terminator, but the block is empty")
  | some lastOp =>
    if !(lastOp.getOpType! ctx.raw).isTerminator then
      throw (named "Expected the last operation of a block to be a terminator")

/-- Check that a graph region contains at most one block. -/
private def WfIRContext.graphRegionsHaveAtMostOneBlock (ctx : WfIRContext OpCode) : Bool :=
  ctx.raw.regions.keys.all fun region =>
    if !region.hasSSADominance ctx then
      let body := region.get! ctx.raw
      body.firstBlock = body.lastBlock
    else
      true

/--
  Check the module-wide invariants needed by LLVM global references: global
  names are unique and every `llvm.mlir.addressof` names a declared global.

  TODO: This is stricter than MLIR, which lets `llvm.mlir.addressof` name either
  an `llvm.mlir.global` or an `llvm.func`, so taking the address of a function
  (function pointers, vtables, globals initialized with a function address) is
  currently rejected.
-/
private def WfIRContext.verifyLLVMGlobalSymbols (ctx : WfIRContext OpCode) :
    Except String Unit := do
  let mut globals : Std.HashMap ByteArray OperationPtr := Std.HashMap.emptyWithCapacity
  for op in ctx.raw.operations.keys do
    if op.getOpType! ctx.raw = .llvm .mlir__global then
      let props := op.getProperties! ctx.raw Llvm.mlir__global
      let symbolName := "@".toUTF8 ++ props.sym_name.value
      if globals.contains symbolName then
        let displayName := String.fromUTF8? symbolName |>.getD "<non-UTF8 global symbol>"
        throw s!"llvm.mlir.global: duplicate global symbol '{displayName}'"
      globals := globals.insert symbolName op
  for op in ctx.raw.operations.keys do
    if op.getOpType! ctx.raw = .llvm .mlir__addressof then
      let props := op.getProperties! ctx.raw Llvm.mlir__addressof
      if !globals.contains props.global_name.value.toUTF8 then
        throw s!"llvm.mlir.addressof: symbol '{props.global_name.value}' does not name an llvm.mlir.global"

/--
  Check the whole-pattern invariants that MLIR verifies in
  `PatternOp::verifyRegions`: a `pdl.pattern` body holds only `pdl` operations,
  and contains at least one `pdl.operation`.
-/
private def WfIRContext.verifyPDLPatternBodies (ctx : WfIRContext OpCode) :
    Except String Unit := do
  let mut patternHasOperation : Std.HashMap OperationPtr Bool := Std.HashMap.emptyWithCapacity
  for op in ctx.raw.operations.keys do
    if op.getOpType! ctx.raw = .pdl .pattern then
      patternHasOperation := patternHasOperation.insert op false
  for op in ctx.raw.operations.keys do
    match op.getParentOp! ctx.raw with
    | some parent =>
      /- The body of a `pdl.pattern` and the body of the `pdl.rewrite` that
         terminates it both belong to the pattern. -/
      let parentType := parent.getOpType! ctx.raw
      if parentType = .pdl .pattern || parentType = .pdl .rewrite then
        let opType := op.getOpType! ctx.raw
        let .pdl pdlOp := opType
          | throw s!"pdl.pattern: expected only `pdl` operations within the pattern body, but got '{String.fromUTF8! opType.name}'"
        if pdlOp = .operation && parentType = .pdl .pattern then
          patternHasOperation := patternHasOperation.insert parent true
    | none => pure ()
  for (_, hasOperation) in patternHasOperation.toArray do
    if !hasOperation then
      throw "pdl.pattern: the pattern must contain at least one `pdl.operation`"

public section

/--
Verify the structural invariants of the IR context and the local invariants of all its operations.
-/
def WfIRContext.verify (ctx : WfIRContext OpCode) : Except String Unit := do
  if !ctx.successorsHaveSameParent then
    throw "Block successors must belong to the same region as their predecessor"
  if !ctx.graphRegionsHaveAtMostOneBlock then
    throw "Graph regions may contain at most one block"
  ctx.raw.forOpsDepM (fun op opIn => do
    let opType := op.getOpType ctx.raw opIn
    let opName := String.fromUTF8! opType.name
    Except.mapError
      (fun msg => if opName.isEmpty || msg.startsWith opName then msg else s!"{opName}: {msg}")
      (do
        op.verifyLocalInvariants ctx opIn
        match (op.get ctx.raw opIn).parent with
        | some _ => op.verifyTerminatorPosition ctx opIn
        | none => pure ()
        op.verifyOperandIsolation ctx opIn))
  ctx.raw.forBlocksDepM (fun block blockIn =>
    block.verifyTerminator ctx blockIn)
  ctx.verifyLLVMGlobalSymbols
  ctx.verifyPDLPatternBodies

attribute [simp] OpCode.verifyLocalInvariants HasOpInfo.verifyLocalInvariants
  OperationPtr.verifyLocalInvariants
  Llvm.verifyLocalInvariants Arith.verifyLocalInvariants Mod_Arith.verifyLocalInvariants

/--
Assert that the IR context satisfies its structural and local invariants.
-/
def WfIRContext.Verified (ctx : WfIRContext OpCode) : Prop :=
  ctx.verify = .ok ()

/-- A verified context satisfies the same-parent successor check. -/
private theorem WfIRContext.Verified.successorsHaveSameParent
    {ctx : WfIRContext OpCode} (ctxVerified : ctx.Verified) :
    ctx.successorsHaveSameParent := by
  simp only [WfIRContext.Verified, WfIRContext.verify] at ctxVerified
  split at ctxVerified
  · trivial
  · grind

/-- Every successor of a block in a verified context belongs to the block's parent region. -/
@[grind →]
theorem WfIRContext.Verified.successor_parent
    {ctx : WfIRContext OpCode} (ctxVerified : ctx.Verified)
    {source : BlockPtr} (sourceIn : source.InBounds ctx.raw)
    (hsourceParent : (source.get! ctx.raw).parent = some region)
    (hsuccessor : successor ∈ source.getSuccessors! ctx.raw) :
    (successor.get! ctx.raw).parent = some region := by
  have hcheck := ctxVerified.successorsHaveSameParent
  have hsourceKeys : source ∈ ctx.raw.blocks.keys := by grind [source.inBounds_def]
  grind [Array.getElem_of_mem hsuccessor, (List.all_eq_true.mp hcheck) source hsourceKeys]

/-- A verified context satisfies the single-block graph-region check. -/
private theorem WfIRContext.Verified.graphRegionsHaveAtMostOneBlock
    {ctx : WfIRContext OpCode} (ctxVerified : ctx.Verified) :
    ctx.graphRegionsHaveAtMostOneBlock := by
  simp only [WfIRContext.Verified, WfIRContext.verify] at ctxVerified
  split at ctxVerified
  · trivial
  · split at ctxVerified
    · trivial
    · grind

/-- The first and last block of a graph region in a verified context are the same. -/
@[grind →]
theorem WfIRContext.Verified.graph_region_firstBlock_eq_lastBlock
    {ctx : WfIRContext OpCode} (ctxVerified : ctx.Verified)
    {region : RegionPtr} (regionIn : region.InBounds ctx.raw)
    (hregionKind : ¬ region.hasSSADominance ctx) :
    (region.get! ctx.raw).firstBlock = (region.get! ctx.raw).lastBlock := by
  have hcheck := ctxVerified.graphRegionsHaveAtMostOneBlock
  have hregionKeys : region ∈ ctx.raw.regions.keys := by grind [region.inBounds_def]
  have hregionCheck := (List.all_eq_true.mp hcheck) region hregionKeys
  grind

/--
Assert that a given operation satisfies its local invariants.
-/
def OperationPtr.Verified (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds ctx.raw := by grind) : Prop :=
  op.verifyLocalInvariants ctx opInBounds = .ok ()

/--
If the context satisfies the invariants of all operations, any operation in bounds is verified.
-/
@[grind →]
axiom OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants {ctx : WfIRContext OpCode}
    {op : OperationPtr} (ctxVerify : ctx.Verified) (opInBounds : op.InBounds ctx.raw := by grind) :
    op.Verified ctx opInBounds

/-!
## Lemmas for verified operations

These are the lemmas that give the information about the structure of verified operations.
There is one lemma per operation, and they are all of the same form: given that an operation
satisfies its local invariants, we can conclude that it has the expected number of operands,
results, regions, and successors, and that the types of its operands and results are as expected.
-/
/--
  Reduce a verified integer binary operation to a successful `verifyIntegerBinop` check.
  The hypothesis `armReduces` says the operation's local-invariant check is exactly the
  `verifyIntegerBinop` arm; it is discharged per operation by unfolding the dispatcher at the
  concrete opcode.
-/
private theorem OperationPtr.verifyIntegerBinop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerBinop ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerBinop ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyIntegerBinop ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

theorem OperationPtr.Verified.arith_constant {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .constant) :
    op.getNumResults! ctx.raw = 1 ∧
    op.getNumOperands! ctx.raw = 0 ∧
    op.getNumSuccessors! ctx.raw = 0 ∧
    op.getNumRegions! ctx.raw = 0 ∧
    ((op.getResult 0).get! ctx.raw).type =
      Attribute.asType (op.getProperties! ctx.raw Arith.constant).value.type (by grind) := by
  simp only [Verified, verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    OpCode.verifyLocalInvariants, Arith.verifyLocalInvariants,
    ← getOpType!_eq_getOpType, opType, ne_eq,
    bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, dite_not,
    ite_not] at opVerify
  simp only [TypeAttr.inj]
  grind

/-- A verified `llvm.mlir.constant` whose value attribute is an integer has an integer result type. -/
theorem OperationPtr.Verified.llvm_mlir__constant_resultType {op : OperationPtr} {opInBounds}
    {intAttr : IntegerAttr}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .mlir__constant)
    (hProp : (op.getProperties! ctx.raw Llvm.mlir__constant).value = .integer intAttr) :
    ∃ intTy : IntegerType, ((op.getResult 0).get! ctx.raw).type.val = .integerType intTy := by
  rw [Verified] at opVerify
  simp only [verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    OpCode.verifyLocalInvariants, Llvm.verifyLocalInvariants,
    ← getOpType!_eq_getOpType, opType] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  simp only [verifyPlainOpCounts, hProp, ne_eq, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure] at opVerify
  cases hty : ((op.getResult 0).get! ctx.raw).type.val with
  | integerType intTy => exact ⟨intTy, rfl⟩
  | _ =>
    rw [hty] at opVerify
    split at opVerify <;> simp_all [reduceCtorEq]

/--
  The structural facts shared by every verified `llvm.icmp`: exactly 2 operands and 1 result, no
  regions or successors, an `i1` result, and the two operands share a single type. Unlike
  `IsVerifiedIntegerBinop`, the operands need not be integers (`llvm.icmp` also compares pointers),
  so only their mutual equality is recorded.
-/
def OperationPtr.IsVerifiedIcmp (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 2 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  (∃ i1ty : IntegerType,
    ((op.getResult 0).get! ctx.raw).type.val = .integerType i1ty ∧ i1ty.bitwidth = 1) ∧
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
    = ((op.getOperand! ctx.raw 1).getType! ctx.raw).val

/-- Structural facts extracted from a successful `verifyLLVMICmp` check. -/
private theorem OperationPtr.verifyLLVMICmp_eq_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (h : op.verifyLLVMICmp ctx opInBounds = .ok ()) :
    op.IsVerifiedIcmp ctx := by
  simp only [IsVerifiedIcmp, verifyLLVMICmp, verifyPlainOpCounts, verifyOperandTypesMatch,
    TypeAttr.verifyIntegerOrPointerType, TypeAttr.verifyI1, ne_eq, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> grind

private theorem OperationPtr.verifyLLVMICmp_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyLLVMICmp ctx opInBounds >>= fun _ => pure ())) :
    op.verifyLLVMICmp ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyLLVMICmp ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/-- Structural facts from the verifier for a verified `llvm.icmp`. -/
theorem OperationPtr.Verified.llvm_icmp {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .icmp) :
    op.IsVerifiedIcmp ctx :=
  op.verifyLLVMICmp_eq_ok <| op.verifyLLVMICmp_ok_of_Verified opVerify <| by
    simp [OperationPtr.verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/--
  Every integer binary operation's `Verified.*` lemma: given that the operation is verified and
  has the given binary-operation opcode, it satisfies `IsVerifiedIntegerBinop`. Each is a thin
  wrapper that reduces `op.Verified` to a successful `verifyIntegerBinop` and applies the
  workhorse `verifyIntegerBinop_eq_ok`.
-/
private theorem OperationPtr.Verified.integerBinop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerBinop ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedIntegerBinop ctx :=
  op.verifyIntegerBinop_eq_ok <| op.verifyIntegerBinop_ok_of_Verified opVerify armReduces
private theorem OperationPtr.verifySelectTypes_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifySelectTypes ctx opInBounds >>= fun _ => pure ())) :
    op.verifySelectTypes ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifySelectTypes ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

theorem OperationPtr.Verified.llvm_select {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .select) :
    op.IsVerifiedSelect ctx :=
  op.verifySelectTypes_eq_ok <| op.verifySelectTypes_ok_of_Verified opVerify <| by
    simp [← getOpType!_eq_getOpType, opType]

/--
  Structural facts guaranteed by a successful `verifyLLVMShift` check. Unlike `IsVerifiedIntegerBinop`
  it does *not* pin the two operands to the same type: `verifyLLVMShift` only requires the shift
  amount (operand 1) to be an integer, and the result to match operand 0 (which may be an integer or
  a byte). The equality of the two operand widths is a *dynamic* fact recovered from a successful
  interpretation, not a static one.
-/
def OperationPtr.IsVerifiedLLVMShift (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 2 ∧
  ((op.getResult 0).get! ctx.raw).type.val = ((op.getOperand! ctx.raw 0).getType! ctx.raw).val ∧
  ∃ intType, ((op.getOperand! ctx.raw 1).getType! ctx.raw).val = .integerType intType

private theorem OperationPtr.verifyLLVMShift_eq_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (h : op.verifyLLVMShift ctx opInBounds = .ok ()) :
    op.IsVerifiedLLVMShift ctx := by
  simp only [IsVerifiedLLVMShift] at ⊢
  simp [verifyLLVMShift, verifyPlainOpCounts, verifyResultTypeMatches,
    TypeAttr.verifyIntegerType, TypeAttr.verifyIntegerOrByteType, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  grind [getNumOperands!_eq_getNumOperands, getNumResults!_eq_getNumResults]

private theorem OperationPtr.verifyLLVMShift_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyLLVMShift ctx opInBounds >>= fun _ => pure ())) :
    op.verifyLLVMShift ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyLLVMShift ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

private theorem OperationPtr.Verified.llvmShift {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyLLVMShift ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedLLVMShift ctx :=
  op.verifyLLVMShift_eq_ok <| op.verifyLLVMShift_ok_of_Verified opVerify armReduces

theorem OperationPtr.Verified.llvm_shl {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .shl) :
    op.IsVerifiedLLVMShift ctx := OperationPtr.Verified.llvmShift opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_lshr {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .lshr) :
    op.IsVerifiedLLVMShift ctx := OperationPtr.Verified.llvmShift opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_addi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .addi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_andi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .andi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ceildivsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ceildivsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ceildivui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ceildivui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_divsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .divsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_divui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .divui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_floordivsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .floordivsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_maxsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .maxsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_maxui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .maxui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_minsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .minsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_minui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .minui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_muli {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .muli) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ori {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ori) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_remsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .remsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_remui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .remui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shli {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shli) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shrsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shrsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shrui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shrui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_subi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .subi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_xori {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .xori) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_and {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .and) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_or {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .or) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_xor {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .xor) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

/--
  Structural facts guaranteed by the verifier for `llvm.mlir.constant`: no operands, one
  result, no successors or regions.
-/
theorem OperationPtr.Verified.llvm_mlir__constant {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .mlir__constant) :
    op.getNumResults! ctx.raw = 1 ∧
    op.getNumOperands! ctx.raw = 0 ∧
    op.getNumSuccessors! ctx.raw = 0 ∧
    op.getNumRegions! ctx.raw = 0 := by
  simp only [Verified, verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    OpCode.verifyLocalInvariants, Llvm.verifyLocalInvariants, ← getOpType!_eq_getOpType, opType,
    verifyPlainOpCounts, ne_eq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure] at opVerify
  grind

theorem OperationPtr.Verified.llvm_intr__smax {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__smax) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__smin {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__smin) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__umax {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__umax) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__umin {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__umin) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__usub__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__usub__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__uadd__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__uadd__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__sadd__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__sadd__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__ssub__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__ssub__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__sshl__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__sshl__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__ushl__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__ushl__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

/--
  Reduce a verified integer unary operation to a successful `verifyIntegerUnop` check.
  The hypothesis `armReduces` says the operation's local-invariant check is exactly the
  `verifyIntegerUnop` arm; it is discharged per operation by unfolding the dispatcher at the
  concrete opcode.
-/
private theorem OperationPtr.verifyIntegerUnop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerUnop ctx opInBounds >>= fun _ => pure ())) :
    ∃ ty, op.verifyIntegerUnop ctx opInBounds = .ok ty := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyIntegerUnop ctx opInBounds with
  | ok ty => exact ⟨ty, rfl⟩
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/-- Structural facts from the verifier for a verified `llvm.intr.bitreverse`. Its verifier arm is
    the shared `verifyIntegerUnop >>= pure` shape, so it reduces like `ctlz`/`cttz`/`ctpop`. -/
theorem OperationPtr.Verified.llvm_intr__bitreverse {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__bitreverse) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp [← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty

/-- Structural facts from the verifier for a verified `llvm.intr.ctlz`. -/
theorem OperationPtr.Verified.llvm_intr__ctlz {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__ctlz) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp [← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty

/-- Structural facts from the verifier for a verified `llvm.intr.cttz`. -/
theorem OperationPtr.Verified.llvm_intr__cttz {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__cttz) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp [← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty

/-- Structural facts from the verifier for a verified `llvm.intr.ctpop`. -/
theorem OperationPtr.Verified.llvm_intr__ctpop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__ctpop) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp [← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty


/-- Structural facts from the verifier for a verified `llvm.intr.abs`. Its verifier arm is exactly
    the shared `verifyIntegerUnop >>= pure` shape (the `is_int_min_poison` property is not checked
    structurally), so it reduces like the `ctlz`/`cttz`/`ctpop` lemmas. -/
theorem OperationPtr.Verified.llvm_intr__abs {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__abs) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp [← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty


/-- Structural facts from the verifier for a verified `llvm.intr.bswap`. Unlike the other unary
    intrinsics, `bswap`'s verifier arm performs an extra bitwidth check *after* the shared
    `verifyIntegerUnop`, so it is not exactly the `verifyIntegerUnop >>= pure` shape; we extract
    the successful `verifyIntegerUnop` by hand from the leading bind. -/
theorem OperationPtr.Verified.llvm_intr__bswap {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__bswap) :
    op.IsVerifiedIntegerUnop ctx := by
  rw [Verified] at opVerify
  simp only [verifyLocalInvariants, HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    Llvm.verifyLocalInvariants, ← getOpType!_eq_getOpType, opType] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  simp only [bind, Except.bind] at opVerify
  obtain ⟨ty, hty⟩ : ∃ ty, op.verifyIntegerUnop ctx opInBounds = .ok ty := by
    cases hb : op.verifyIntegerUnop ctx opInBounds with
    | ok ty => exact ⟨ty, rfl⟩
    | error e => rw [hb] at opVerify; simp at opVerify
  exact op.verifyIntegerUnop_eq_ok hty

/--
  Reduce a verified integer ternary operation to a successful `verifyIntegerTernop` check.
  `armReduces` says the operation's local-invariant check is exactly the `verifyIntegerTernop`
  arm; it is discharged per operation by unfolding the dispatcher at the concrete opcode.
-/
private theorem OperationPtr.verifyIntegerTernop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerTernop ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerTernop ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyIntegerTernop ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/--
  Every integer ternary operation's `Verified.*` lemma reduces to this: given a verified operation
  whose local-invariant check is the `verifyIntegerTernop` arm, it satisfies
  `IsVerifiedIntegerTernop`.
-/
private theorem OperationPtr.Verified.integerTernop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerTernop ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedIntegerTernop ctx :=
  op.verifyIntegerTernop_eq_ok <| op.verifyIntegerTernop_ok_of_Verified opVerify armReduces

/-- Structural facts from the verifier for a verified `llvm.intr.fshl`. -/
theorem OperationPtr.Verified.llvm_intr__fshl {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__fshl) :
    op.IsVerifiedIntegerTernop ctx := OperationPtr.Verified.integerTernop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

/-- Structural facts from the verifier for a verified `llvm.intr.fshr`. -/
theorem OperationPtr.Verified.llvm_intr__fshr {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__fshr) :
    op.IsVerifiedIntegerTernop ctx := OperationPtr.Verified.integerTernop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

/--
  Reduce a verified integer extension operation to a successful `verifyIntegerExtTypes` check.
  `armReduces` says the operation's local-invariant check is exactly the `verifyIntegerExtTypes`
  arm; it is discharged per operation by unfolding the dispatcher at the concrete opcode.
-/
private theorem OperationPtr.verifyIntegerExtTypes_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerExtTypes ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerExtTypes ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyIntegerExtTypes ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/--
  Every integer extension operation's `Verified.*` lemma reduces to this: given a verified
  operation whose local-invariant check is the `verifyIntegerExtTypes` arm, it satisfies
  `IsVerifiedIntegerExtop`.
-/
private theorem OperationPtr.Verified.integerExtop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerExtTypes ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedIntegerExtop ctx :=
  op.verifyIntegerExtTypes_eq_ok <| op.verifyIntegerExtTypes_ok_of_Verified opVerify armReduces

/-- Structural facts from the verifier for a verified `llvm.sext`. -/
theorem OperationPtr.Verified.llvm_sext {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .sext) :
    op.IsVerifiedIntegerExtop ctx := OperationPtr.Verified.integerExtop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

/-- Structural facts from the verifier for a verified `llvm.zext`. -/
theorem OperationPtr.Verified.llvm_zext {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .zext) :
    op.IsVerifiedIntegerExtop ctx := OperationPtr.Verified.integerExtop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_add {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .add) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_sub {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .sub) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_ashr {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .ashr) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_mul {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .mul) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_sdiv {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .sdiv) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_udiv {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .udiv) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_srem {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .srem) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_urem {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .urem) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

/- Verified ModArith Op Lemmas -/

def OperationPtr.IsVerifiedModArithBinop (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 2 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ modArithType,
    modArithType.modulus.value > 0 ∧
    modArithType.modulus.value < 2 ^ modArithType.modulus.type.bitwidth ∧
    ((op.getResult 0).get! ctx.raw).type = Attribute.asType (.modArithType modArithType) (by grind) ∧
    ((op.getOperand! ctx.raw 0).getType! ctx.raw) = Attribute.asType (.modArithType modArithType) (by grind) ∧
    ((op.getOperand! ctx.raw 1).getType! ctx.raw) = Attribute.asType (.modArithType modArithType) (by grind)


private theorem OperationPtr.verifyModArithBinOp_eq_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (h : op.verifyModArithBinOp ctx opInBounds = .ok ()) :
    op.IsVerifiedModArithBinop ctx := by
  simp only [IsVerifiedModArithBinop, TypeAttr.inj]
  simp only [verifyModArithBinOp, verifyPlainOpCounts, verifyOperandTypesMatch,
             verifyResultTypeMatches, TypeAttr.verifyModArithType,
             Except_bind_ok_iff, exists_punit] at h
  obtain ⟨hPlainOpCounts, operandType, hOperandTypesMatch,
          hResultTypeMatches, modArithType, hModArithType, _⟩ := h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
    at hPlainOpCounts hOperandTypesMatch hResultTypeMatches hModArithType
  grind

private theorem OperationPtr.Verified.modArithBinop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyModArithBinOp ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedModArithBinop ctx := by
  rw [Verified, armReduces] at opVerify
  have h : op.verifyModArithBinOp ctx opInBounds = .ok () := by
    cases hb : op.verifyModArithBinOp ctx opInBounds with
    | ok _ => rfl
    | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify
  exact op.verifyModArithBinOp_eq_ok h

theorem OperationPtr.Verified.mod_arith_add {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .mod_arith .add) :
    op.IsVerifiedModArithBinop ctx := OperationPtr.Verified.modArithBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.mod_arith_mul {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .mod_arith .mul) :
    op.IsVerifiedModArithBinop ctx := OperationPtr.Verified.modArithBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.mod_arith_sub {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .mod_arith .sub) :
    op.IsVerifiedModArithBinop ctx := OperationPtr.Verified.modArithBinop opVerify <| by
  simp [← getOpType!_eq_getOpType, opType]

def OperationPtr.IsVerifiedModArithConstant (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumOperands! ctx.raw = 0 ∧
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ modArithType,
    ((op.getResult 0).get! ctx.raw).type = Attribute.asType (.modArithType modArithType) (by grind) ∧
    modArithType.modulus.value > 0 ∧
    modArithType.modulus.value < 2 ^ modArithType.modulus.type.bitwidth ∧
    -(2 ^ (modArithType.modulus.type.bitwidth - 1) : Int)
        ≤ (op.getProperties! ctx.raw Mod_Arith.constant).value.value ∧
    (op.getProperties! ctx.raw Mod_Arith.constant).value.value
        < 2 ^ modArithType.modulus.type.bitwidth

theorem OperationPtr.Verified.mod_arith_constant {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .mod_arith .constant) :
    op.IsVerifiedModArithConstant ctx := by
  simp only [Verified, verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    OpCode.verifyLocalInvariants, Mod_Arith.verifyLocalInvariants,
    ← getOpType!_eq_getOpType, opType] at opVerify
  have h : op.verifyModArithConstantOp ctx opInBounds = .ok () := by
    cases hb : op.verifyModArithConstantOp ctx opInBounds with
    | ok _ => rfl
    | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify
  simp only [IsVerifiedModArithConstant, TypeAttr.inj]
  simp only [verifyModArithConstantOp, verifyPlainOpCounts, TypeAttr.verifyModArithType,
            Except_bind_ok_iff, exists_punit] at h
  obtain ⟨hPlainOpCounts, modArithType, hModArithType, hAttr⟩ := h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
    at hPlainOpCounts hModArithType hAttr
  grind

/-- Structural facts guaranteed for a verified `func.func`: it has no operands, results, or
successors, and exactly one region (its body). -/
theorem OperationPtr.Verified.func_func {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .func .func) :
    op.getNumOperands! ctx.raw = 0 ∧
    op.getNumResults! ctx.raw = 0 ∧
    op.getNumSuccessors! ctx.raw = 0 ∧
    op.getNumRegions! ctx.raw = 1 := by
  simp only [Verified, verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    OpCode.verifyLocalInvariants, Func.verifyLocalInvariants,
    ← getOpType!_eq_getOpType, opType, ne_eq, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure, ite_not] at opVerify
  grind

end
end Veir
