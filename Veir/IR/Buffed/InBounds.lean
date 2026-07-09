module

public meta import Veir.IR.Buffed.Meta
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.Basic
public import Veir.IR.Basic
import Veir.IR.InBounds
import Veir.IR.GetSet
import Veir.IR.Grind
import Veir.IR.Buffed.Meta

import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs
import all Veir.IR.Buffed.Sim
import all Veir.IR.Buffed.Basic

public section

namespace Veir.Sim

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]

variable {ctx ctx' : IRContext OpInfo}

section operation

variable {op : OperationPtr} (h : op.InBounds ctx)

@[grind .]
theorem OperationPtr.inBounds_of_optionPtr_inBounds (optr : Sim.OptionOperationPtr) (ib : optr.InBounds ctx) ptr :
    optr.toOption = some ptr →
    ptr.InBounds ctx := by
  grind

grind_pattern [inbounds] OperationPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

@[grind .]
theorem OptionOperationPtr.toO_inBounds_of_inBounds (ptr : Sim.OperationPtr) :
    ptr.InBounds ctx → ptr.toO.InBounds ctx := by
  grind [OperationPtr.toO]

@[grind .]
theorem OptionOperationPtr.none_inBounds : none.InBounds ctx := by
  simp [none]
  constructor
  · simp [Sim, Veir.OperationPtr.toO]
  · grind

-- @[grind =]
-- theorem OptionOperationPtr.inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (ptr' : Sim.GenericPtr)
--     (next : Sim.OptionOperationPtr) h₁ h₂ :
--     ptr'.InBounds (setNextOp ctx ptr next h₁ h₂) ↔ ptr'.InBounds ctx := by
--   grind

@[grind =]
theorem OperationPtr.setNextOp_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (ptr' : Sim.GenericPtr)
    (next : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setNextOp ctx ptr next h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setNextOp_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (ptr' : Veir.GenericPtr)
    (next : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setNextOp ctx ptr next h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem OperationPtr.setPrevOp_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (ptr' : Sim.GenericPtr)
    (prev : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setPrevOp ctx ptr prev h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setPrevOp_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (ptr' : Veir.GenericPtr)
    (prev : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setPrevOp ctx ptr prev h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem OperationPtr.setParent_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (ptr' : Sim.GenericPtr)
    (parent : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setParent ctx ptr parent h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setParent_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (ptr' : Veir.GenericPtr)
    (parent : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setParent ctx ptr parent h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind .]
theorem OperationPtr.getOpOperand_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i.toNat < op.spec.getNumOperands! ctx.spec) :
    (op.getOperandPtr ctx i hop).InBounds ctx := by
  sorry
  -- grind

@[grind .]
theorem OperationPtr.getBlockOperand_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i.toNat < op.spec.getNumSuccessors! ctx.spec) :
    (op.getBlockOperandPtr ctx i hop).InBounds ctx := by
  sorry

@[grind .]
theorem OperationPtr.getResult_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i.toNat < op.spec.getNumResults! ctx.spec) :
    (op.getResultPtr ctx i hop).InBounds ctx := by
  sorry

@[grind =>]
theorem OperationPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr)
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .fromOperation ptr') := by
  sorry

theorem OperationPtr.allocEmpty_operationPtr_iff (ptr : OperationPtr)
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr =  ptr') := by
  grind [generic_ptr_grind, Sim.OperationPtr]

@[grind . ]
theorem OperationPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr)
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem OperationPtr.allocEmpty_newBlock_inBounds
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr'.InBounds ctx' := by
  sorry

@[grind .]
theorem OperationPtr.allocEmpty_newBlock_veir_inBounds {ptr : Veir.GenericPtr}
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  sorry

@[grind .]
theorem OperationPtr.allocEmpty_not_inBounds
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ¬ ptr'.spec.InBounds ctx.spec := by
  sorry

-- @[grind →]
-- theorem OpResultPtr.dealloc.inBounds_genericPtr_of_inBounds_dealloc {ptr : GenericPtr} :
--     ptr.InBounds (OperationPtr.dealloc op ctx inBounds) → ptr.InBounds ctx := by
--   grind

-- theorem OpResultPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc {opResult : OpResultPtr} :
--     opResult.InBounds (OperationPtr.dealloc op' ctx inBounds) → opResult.op ≠ op' := by
--   grind

-- theorem OpOperandPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc {opOperand : OpOperandPtr} :
--     opOperand.InBounds (OperationPtr.dealloc op' ctx inBounds) → opOperand.op ≠ op' := by
--   grind

-- theorem BlockOperandPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
--     blockOperand.InBounds (OperationPtr.dealloc op' ctx inBounds) → blockOperand.op ≠ op' := by
--   grind

end operation

/- OpOperandPtr -/

section opoperand

attribute [local grind] OpOperandPtr.setNextUse OpOperandPtr.setBack OpOperandPtr.setOwner OpOperandPtr.setValue

variable {opOperand : OpOperandPtr} (h : opOperand.InBounds ctx)

@[grind .]
theorem OpOperandPtr.inBounds_of_optionPtr_inBounds (optr : Sim.OptionOpOperandPtr) (ib : optr.InBounds ctx) ptr :
    optr.toOption = some ptr →
    ptr.InBounds ctx := by
  grind

grind_pattern [inbounds] OpOperandPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

@[grind .]
theorem OptionOpOperandPtr.toO_inBounds_of_inBounds (ptr : Sim.OpOperandPtr) :
    ptr.InBounds ctx → ptr.toO.InBounds ctx := by
  grind [OpOperandPtr.toO]

@[grind .]
theorem OptionOpOperandPtr.none_inBounds : none.InBounds ctx := by
  simp [none]
  constructor
  · simp [Sim, Veir.OpOperandPtr.toO]
  · grind

@[grind =]
theorem OpOperandPtr.setNextUse_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ptr' : Sim.GenericPtr)
    (nextUse : Sim.OptionOpOperandPtr) h₁ h₂ :
    ptr'.InBounds (setNextUse ctx ptr nextUse h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem OpOperandPtr.setNextUse_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ptr' : Veir.GenericPtr)
    (nextUse : Sim.OptionOpOperandPtr) h₁ h₂ :
    ptr'.InBounds (setNextUse ctx ptr nextUse h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem OpOperandPtr.setBack_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ptr' : Sim.GenericPtr)
    (back : Sim.OpOperandPtrPtr) h₁ h₂ :
    ptr'.InBounds (setBack ctx ptr back h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem OpOperandPtr.setBack_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ptr' : Veir.GenericPtr)
    (back : Sim.OpOperandPtrPtr) h₁ h₂ :
    ptr'.InBounds (setBack ctx ptr back h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem OpOperandPtr.setOwner_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ptr' : Sim.GenericPtr)
    (owner : Sim.OperationPtr) h₁ h₂ :
    ptr'.InBounds (setOwner ctx ptr owner h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem OpOperandPtr.setOwner_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ptr' : Veir.GenericPtr)
    (owner : Sim.OperationPtr) h₁ h₂ :
    ptr'.InBounds (setOwner ctx ptr owner h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem OpOperandPtr.setValue_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ptr' : Sim.GenericPtr)
    (value : Sim.ValuePtr) h₁ h₂ :
    ptr'.InBounds (setValue ctx ptr value h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem OpOperandPtr.setValue_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ptr' : Veir.GenericPtr)
    (value : Sim.ValuePtr) h₁ h₂ :
    ptr'.InBounds (setValue ctx ptr value h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

-- theorem OpOperandPtr.inBounds_if_operand_size_eq :
--     (OperationPtr.getNumOperands opPtr ctx opIn = OperationPtr.getNumOperands opPtr' ctx' op'In) ↔
--     (∀ index, (OpOperandPtr.mk opPtr index).InBounds ctx ↔ (OpOperandPtr.mk opPtr' index).InBounds ctx') := by
--   constructor
--   · grind
--   · intro hi
--     apply Nat.eq_iff_forall_lessthan
--     intros i
--     have := hi i
--     grind

end opoperand

section opresult

variable {opRes : OpResultPtr} (h : opRes.InBounds ctx)

@[grind .]
theorem OpResultPtr.inBounds_of_optionPtr_inBounds (optr : Sim.OptionOpResultPtr) (ib : optr.InBounds ctx) ptr :
    optr.toOption = some ptr →
    ptr.InBounds ctx := by
  grind

grind_pattern [inbounds] OpResultPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

@[grind .]
theorem OptionOpResultPtr.toO_inBounds_of_inBounds (ptr : Sim.OpResultPtr) :
    ptr.InBounds ctx → ptr.toO.InBounds ctx := by
  grind [OpResultPtr.toO]

@[grind .]
theorem OptionOpResultPtr.none_inBounds : none.InBounds ctx := by
  simp [none]
  constructor
  · simp [Sim, Veir.OpResultPtr.toO]
  · grind

@[grind =]
theorem OpResultPtr.setOwner_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) (ptr' : Sim.GenericPtr)
    (owner : Sim.OperationPtr) h₁ h₂ :
    ptr'.InBounds (setOwner ctx ptr owner h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem OpResultPtr.setOwner_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) (ptr' : Veir.GenericPtr)
    (owner : Sim.OperationPtr) h₁ h₂ :
    ptr'.InBounds (setOwner ctx ptr owner h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

end opresult

section blockargument

variable {ba : BlockArgumentPtr}

@[grind .]
theorem BlockArgumentPtr.inBounds_of_optionPtr_inBounds (optr : Sim.OptionBlockArgumentPtr) (ib : optr.InBounds ctx) ptr :
    optr.toOption = some ptr →
    ptr.InBounds ctx := by
  grind

grind_pattern [inbounds] BlockArgumentPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

@[grind .]
theorem OptionBlockArgumentPtr.toO_inBounds_of_inBounds (ptr : Sim.BlockArgumentPtr) :
    ptr.InBounds ctx → ptr.toO.InBounds ctx := by
  grind [BlockArgumentPtr.toO]

@[grind .]
theorem OptionBlockArgumentPtr.none_inBounds : none.InBounds ctx := by
  simp [none]
  constructor
  · simp [Sim, Veir.BlockArgumentPtr.toO]
  · grind

@[grind =]
theorem BlockArgumentPtr.setFirstUse_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) (ptr' : Sim.GenericPtr)
    (firstUse : Sim.OptionOpOperandPtr) h₁ h₂ :
    ptr'.InBounds (setFirstUse ctx ptr firstUse h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.setFirstUse_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) (ptr' : Veir.GenericPtr)
    (firstUse : Sim.OptionOpOperandPtr) h₁ h₂ :
    ptr'.InBounds (setFirstUse ctx ptr firstUse h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

end blockargument

section value

variable {value : ValuePtr} (h : value.InBounds ctx)

@[grind .]
theorem ValuePtr.inBounds_of_optionPtr_inBounds (optr : Sim.OptionValuePtr) (ib : optr.InBounds ctx) ptr :
    optr.toOption = some ptr →
    ptr.InBounds ctx := by
  grind

grind_pattern [inbounds] ValuePtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

@[grind .]
theorem OptionValuePtr.toO_inBounds_of_inBounds (ptr : Sim.ValuePtr) :
    ptr.InBounds ctx → ptr.toO.InBounds ctx := by
  grind [ValuePtr.toO]

@[grind .]
theorem OptionValuePtr.none_inBounds : none.InBounds ctx := by
  simp [none]
  constructor
  · simp [Sim, Veir.ValuePtr.toO]
  · grind

@[grind =]
theorem ValuePtr.setFirstUse_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr) (ptr' : Sim.GenericPtr)
    (firstUse : Sim.OptionOpOperandPtr) h₁ h₂ :
    ptr'.InBounds (setFirstUse ctx ptr firstUse h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem ValuePtr.setFirstUse_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr) (ptr' : Veir.GenericPtr)
    (firstUse : Sim.OptionOpOperandPtr) h₁ h₂ :
    ptr'.InBounds (setFirstUse ctx ptr firstUse h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem ValuePtr.fromOpResult_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) :
    (fromOpResultPtr ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  simp [fromOpResultPtr]
  constructor <;> grind

@[grind =]
theorem ValuePtr.fromBlockArgument_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) :
    (fromBlockArgumentPtr ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  simp [fromBlockArgumentPtr]
  constructor <;> grind

end value

section block

variable {block : BlockPtr} (h : block.InBounds ctx)

@[grind .]
theorem BlockPtr.inBounds_of_optionPtr_inBounds (optr : Sim.OptionBlockPtr) (ib : optr.InBounds ctx) ptr :
    optr.toOption = some ptr →
    ptr.InBounds ctx := by
  grind

grind_pattern [inbounds] BlockPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

@[grind .]
theorem OptionBlockPtr.toO_inBounds_of_inBounds (ptr : Sim.BlockPtr) :
    ptr.InBounds ctx → ptr.toO.InBounds ctx := by
  grind [BlockPtr.toO]

@[grind .]
theorem OptionBlockPtr.none_inBounds : none.InBounds ctx := by
  simp [none]
  constructor
  · simp [Sim, Veir.BlockPtr.toO]
  · grind

@[grind .]
theorem BlockPtr.getArgument_inBounds (block : BlockPtr)
    (hblock : block.InBounds ctx) i (h₂ : i.toNat < block.spec.getNumArguments ctx.spec) :
    (block.getArgumentPtr ctx i hblock).InBounds ctx := by
  -- grind
  sorry

@[grind =]
theorem BlockPtr.setParent_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Sim.GenericPtr)
    (parent : Sim.OptionRegionPtr) h₁ h₂ :
    ptr'.InBounds (setParent ctx ptr parent h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setParent_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Veir.GenericPtr)
    (parent : Sim.OptionRegionPtr) h₁ h₂ :
    ptr'.InBounds (setParent ctx ptr parent h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem BlockPtr.setFirstUse_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Sim.GenericPtr)
    (firstUse : Sim.OptionBlockOperandPtr) h₁ h₂ :
    ptr'.InBounds (setFirstUse ctx ptr firstUse h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setFirstUse_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Veir.GenericPtr)
    (firstUse : Sim.OptionBlockOperandPtr) h₁ h₂ :
    ptr'.InBounds (setFirstUse ctx ptr firstUse h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem BlockPtr.setFirstOp_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Sim.GenericPtr)
    (firstOp : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setFirstOp ctx ptr firstOp h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setFirstOp_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Veir.GenericPtr)
    (firstOp : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setFirstOp ctx ptr firstOp h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem BlockPtr.setLastOp_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Sim.GenericPtr)
    (lastOp : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setLastOp ctx ptr lastOp h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setLastOp_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Veir.GenericPtr)
    (lastOp : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setLastOp ctx ptr lastOp h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem BlockPtr.setNextBlock_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Sim.GenericPtr)
    (next : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setNextBlock ctx ptr next h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setNextBlock_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Veir.GenericPtr)
    (next : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setNextBlock ctx ptr next h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem BlockPtr.setPrevBlock_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Sim.GenericPtr)
    (prev : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setPrevBlock ctx ptr prev h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setPrevBlock_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) (ptr' : Veir.GenericPtr)
    (prev : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setPrevBlock ctx ptr prev h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =>]
theorem BlockPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr) (heq : allocEmpty ctx numArgs = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .fromBlock ptr' ∨ ptr = .fromBlockOperandPtr (ptr'.getBlockOperandPtrPtr)) := by
  sorry

@[grind .]
theorem BlockPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr) (heq : allocEmpty ctx numArgs = some (ptr', ctx')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem BlockPtr.allocEmpty_genericPtr_veir_mono (ptr : Veir.GenericPtr) (heq : allocEmpty ctx numArgs = some (ptr', ctx')) :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  simp [allocEmpty] at heq
  -- `allocEmpty` now guards on `numArgs ≤ countCard`; `simp` turns the `if` into `∃ h, …`, so
  -- destructure the guard proof before splitting on the `allocEmptyImpl` match.
  obtain ⟨hguard, heq⟩ := heq
  split at heq
  · grind [generic_ptr_grind]
  · simp_all
    obtain ⟨a, b⟩ := heq
    subst ctx'
    sorry

@[grind .]
theorem BlockPtr.allocEmpty_newBlock_inBounds (heq : allocEmpty ctx numArgs = some (ptr', ctx')) :
    ptr'.InBounds ctx' := by
  have : (GenericPtr.fromBlock ptr').InBounds ctx' := by grind
  grind [generic_ptr_grind]

end block

section region

variable {region : RegionPtr} (h : region.InBounds ctx)

@[grind .]
theorem RegionPtr.inBounds_of_optionPtr_inBounds (optr : Sim.OptionRegionPtr) (ib : optr.InBounds ctx) ptr :
    optr.toOption = some ptr →
    ptr.InBounds ctx := by
  grind

grind_pattern [inbounds] RegionPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

@[grind .]
theorem OptionRegionPtr.toO_inBounds_of_inBounds (ptr : Sim.RegionPtr) :
    ptr.InBounds ctx → ptr.toO.InBounds ctx := by
  grind [RegionPtr.toO]

@[grind .]
theorem OptionRegionPtr.none_inBounds : none.InBounds ctx := by
  simp [none]
  constructor
  · simp [Sim, Veir.RegionPtr.toO]
  · grind

@[grind =]
theorem RegionPtr.setParent_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ptr' : Sim.GenericPtr)
    (parent : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setParent ctx ptr parent h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem RegionPtr.setParent_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ptr' : Veir.GenericPtr)
    (parent : Sim.OptionOperationPtr) h₁ h₂ :
    ptr'.InBounds (setParent ctx ptr parent h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem RegionPtr.setFirstBlock_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ptr' : Sim.GenericPtr)
    (firstBlock : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setFirstBlock ctx ptr firstBlock h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem RegionPtr.setFirstBlock_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ptr' : Veir.GenericPtr)
    (firstBlock : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setFirstBlock ctx ptr firstBlock h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem RegionPtr.setLastBlock_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ptr' : Sim.GenericPtr)
    (lastBlock : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setLastBlock ctx ptr lastBlock h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem RegionPtr.setLastBlock_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ptr' : Veir.GenericPtr)
    (lastBlock : Sim.OptionBlockPtr) h₁ h₂ :
    ptr'.InBounds (setLastBlock ctx ptr lastBlock h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

-- @[grind =>]
-- theorem RegionPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr) (heq : allocEmpty ctx = some (ptr', ctx')) :
--     ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .fromRegion ptr') := by
  -- constructor
  -- · grind
  -- · grind

-- @[grind .]
-- theorem RegionPtr.allocEmpty_newBlock_inBounds (heq : allocEmpty ctx = some (ptr, ctx')) :
--     ptr.InBounds ctx' := by
--   simp [allocEmpty] at heq


-- @[grind .]
-- theorem RegionPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
--     ptr.InBounds ctx → ptr.InBounds ctx' := by
--   grind

end region

section blockoperand

variable {blockOperand : BlockOperandPtr} (h : blockOperand.InBounds ctx)

@[grind .]
theorem BlockOperandPtr.inBounds_of_optionPtr_inBounds (optr : Sim.OptionBlockOperandPtr) (ib : optr.InBounds ctx) ptr :
    optr.toOption = some ptr →
    ptr.InBounds ctx := by
  grind

grind_pattern [inbounds] BlockOperandPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

@[grind .]
theorem OptionBlockOperandPtr.toO_inBounds_of_inBounds (ptr : Sim.BlockOperandPtr) :
    ptr.InBounds ctx → ptr.toO.InBounds ctx := by
  grind [BlockOperandPtr.toO]

@[grind .]
theorem OptionBlockOperandPtr.none_inBounds : none.InBounds ctx := by
  simp [none]
  constructor
  · simp [Sim, Veir.BlockOperandPtr.toO]
  · grind

@[grind =]
theorem BlockOperandPtr.setNextUse_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) (ptr' : Sim.GenericPtr)
    (nextUse : Sim.OptionBlockOperandPtr) h₁ h₂ :
    ptr'.InBounds (setNextUse ctx ptr nextUse h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setNextUse_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) (ptr' : Veir.GenericPtr)
    (nextUse : Sim.OptionBlockOperandPtr) h₁ h₂ :
    ptr'.InBounds (setNextUse ctx ptr nextUse h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem BlockOperandPtr.setBack_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) (ptr' : Sim.GenericPtr)
    (back : Sim.BlockOperandPtrPtr) h₁ h₂ :
    ptr'.InBounds (setBack ctx ptr back h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setBack_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) (ptr' : Veir.GenericPtr)
    (back : Sim.BlockOperandPtrPtr) h₁ h₂ :
    ptr'.InBounds (setBack ctx ptr back h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem BlockOperandPtr.setOwner_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) (ptr' : Sim.GenericPtr)
    (owner : Sim.OperationPtr) h₁ h₂ :
    ptr'.InBounds (setOwner ctx ptr owner h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setOwner_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) (ptr' : Veir.GenericPtr)
    (owner : Sim.OperationPtr) h₁ h₂ :
    ptr'.InBounds (setOwner ctx ptr owner h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

@[grind =]
theorem BlockOperandPtr.setValue_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) (ptr' : Sim.GenericPtr)
    (value : Sim.BlockPtr) h₁ h₂ :
    ptr'.InBounds (setValue ctx ptr value h₁ h₂) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setValue_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) (ptr' : Veir.GenericPtr)
    (value : Sim.BlockPtr) h₁ h₂ :
    ptr'.InBounds (setValue ctx ptr value h₁ h₂).spec ↔ ptr'.InBounds ctx.spec := by
  grind

end blockoperand

section blockOperandPtr

variable {blockOperandPtr : BlockOperandPtrPtr} (h : blockOperandPtr.InBounds ctx)

@[grind =]
theorem BlockOperandPtrPtr.set_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr) (ptr' : Sim.GenericPtr)
    (value : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    ptr'.InBounds (set ctx ptr value ib valueIb) ↔ ptr'.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.set_veir_inBounds (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr) (ptr' : Veir.GenericPtr)
    (value : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    ptr'.InBounds (set ctx ptr value ib valueIb).spec ↔ ptr'.InBounds ctx.spec := by
  grind

end blockOperandPtr
