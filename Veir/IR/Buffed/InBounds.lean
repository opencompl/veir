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

/-- The spec-level operand pointer is in bounds when its index is below the operand count. -/
theorem OperationPtr.getOpOperand_veir_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) (i : UInt64) (h₂ : i.toNat < op.spec.getNumOperands! ctx.spec) :
    (op.spec.getOpOperand i.toNat).InBounds ctx.spec := by
  have hib := hop.ib
  grind [Veir.OperationPtr.getOpOperand_def, Veir.OpOperandPtr.inBounds_def]

/-- The buffer-side operand address computed by `getOperandPtr!` is exactly the buffed address of the spec-level operand pointer `op.spec.getOpOperand i`. -/
theorem OperationPtr.getOpOperand_toM (op : OperationPtr)
    (hop : op.InBounds ctx) (i : UInt64) (h₂ : i.toNat < op.spec.getNumOperands! ctx.spec) :
    (op.spec.getOpOperand i.toNat).toM ctx.spec
      = op.impl + Buffed.OperationMPtr.computeOperandOffset! ctx.buf op.impl i := by
  have hsim := hop.sim
  have hib := hop.ib
  have hri := ctx.sim.repr.operations_indices op.spec hib
  have halt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op.spec hib
  have hsize : ctx.buf.mem.size < 2^63 := by grind
  have hoib := OperationPtr.getOpOperand_veir_inBounds op hop i h₂
  have haop := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) (op.spec.getOpOperand i.toNat) hoib
  have hplus : (Buffed.OperationMPtr.computeOperandOffset! ctx.buf op.impl i).toInt
      = Buffed.Operation.Offsets.operandsInt op.spec ctx.spec + Buffed.OpOperand.sizeNat * i.toNat := by
    simp only [Buffed.OperationMPtr.computeOperandOffset!]
    rw [Int64.add_toInt_lt'] <;>
      grind [layout_grind, UInt64.toNat_mul, OperationPtr.computeOperandsOffset!_ideal]
  have haddr : ((op.impl + Buffed.OperationMPtr.computeOperandOffset! ctx.buf op.impl i).toNat : Int)
      = op.impl.toNat + (Buffed.Operation.Offsets.operandsInt op.spec ctx.spec + Buffed.OpOperand.sizeNat * i.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
  rw [← UInt64.toNat_inj]
  have hflat := Veir.OpOperandPtr.toFlat_ideal (ctx := ctx.spec) (by grind) (op.spec.getOpOperand i.toNat) hoib
  simp only [Veir.OpOperandPtr.toM, hflat]
  grind [layout_grind, Veir.OperationPtr.getOpOperand_def, Nat.toUInt64_eq, UInt64.toNat_ofNat']

@[grind .]
theorem OperationPtr.getOpOperand_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i.toNat < op.spec.getNumOperands! ctx.spec) :
    (op.getOperandPtr ctx i hop).InBounds ctx := by
  rw [Sim.OperationPtr.getOperandPtr_eq_getOperandPtr!]
  exact ⟨OperationPtr.getOpOperand_toM op hop i h₂, OperationPtr.getOpOperand_veir_inBounds op hop i h₂⟩

/-- The spec-level block operand pointer is in bounds when its index is below the count. -/
theorem OperationPtr.getBlockOperand_veir_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) (i : UInt64) (h₂ : i.toNat < op.spec.getNumSuccessors! ctx.spec) :
    (op.spec.getBlockOperand i.toNat).InBounds ctx.spec := by
  have hib := hop.ib
  grind [Veir.OperationPtr.getBlockOperand_def, Veir.BlockOperandPtr.inBounds_def]

/-- The buffer-side block operand address computed by `getBlockOperandPtr!` is exactly the buffed address of the spec-level pointer `op.spec.getBlockOperand i`. -/
theorem OperationPtr.getBlockOperand_toM (op : OperationPtr)
    (hop : op.InBounds ctx) (i : UInt64) (h₂ : i.toNat < op.spec.getNumSuccessors! ctx.spec) :
    (op.spec.getBlockOperand i.toNat).toM ctx.spec
      = op.impl + Buffed.OperationMPtr.computeBlockOperandOffset! ctx.buf op.impl i := by
  have hsim := hop.sim
  have hib := hop.ib
  have hri := ctx.sim.repr.operations_indices op.spec hib
  have halt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op.spec hib
  have hsize : ctx.buf.mem.size < 2^63 := by grind
  have hoib := OperationPtr.getBlockOperand_veir_inBounds op hop i h₂
  have haop := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) (op.spec.getBlockOperand i.toNat) hoib
  have hplus : (Buffed.OperationMPtr.computeBlockOperandOffset! ctx.buf op.impl i).toInt
      = Buffed.Operation.Offsets.blockOperandsInt op.spec ctx.spec + Buffed.BlockOperand.sizeNat * i.toNat := by
    simp only [Buffed.OperationMPtr.computeBlockOperandOffset!]
    rw [Int64.add_toInt_lt'] <;>
      grind [layout_grind, UInt64.toNat_mul, OperationPtr.computeBlockOperandsOffset!_ideal]
  have haddr : ((op.impl + Buffed.OperationMPtr.computeBlockOperandOffset! ctx.buf op.impl i).toNat : Int)
      = op.impl.toNat + (Buffed.Operation.Offsets.blockOperandsInt op.spec ctx.spec + Buffed.BlockOperand.sizeNat * i.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
  rw [← UInt64.toNat_inj]
  have hflat := Veir.BlockOperandPtr.toFlat_ideal (ctx := ctx.spec) (by grind) (op.spec.getBlockOperand i.toNat) hoib
  simp only [Veir.BlockOperandPtr.toM, hflat]
  grind [layout_grind, Veir.OperationPtr.getBlockOperand_def, Nat.toUInt64_eq, UInt64.toNat_ofNat']

@[grind .]
theorem OperationPtr.getBlockOperand_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i.toNat < op.spec.getNumSuccessors! ctx.spec) :
    (op.getBlockOperandPtr ctx i hop).InBounds ctx := by
  rw [Sim.OperationPtr.getBlockOperandPtr_eq_getBlockOperandPtr!]
  exact ⟨OperationPtr.getBlockOperand_toM op hop i h₂, OperationPtr.getBlockOperand_veir_inBounds op hop i h₂⟩

/-- The spec-level result pointer is in bounds when its index is below the result count. -/
theorem OperationPtr.getResult_veir_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) (i : UInt64) (h₂ : i.toNat < op.spec.getNumResults! ctx.spec) :
    (op.spec.getResult i.toNat).InBounds ctx.spec := by
  have hib := hop.ib
  grind [Veir.OperationPtr.getResult_def, Veir.OpResultPtr.inBounds_def]

/-- The buffer-side result address computed by `getResultPtr!` is exactly the buffed address of the spec-level result pointer `op.spec.getResult i`. -/
theorem OperationPtr.getResult_toM (op : OperationPtr)
    (hop : op.InBounds ctx) (i : UInt64) (h₂ : i.toNat < op.spec.getNumResults! ctx.spec) :
    (op.spec.getResult i.toNat).toM ctx.spec
      = op.impl + Buffed.OperationMPtr.computeResultOffset! ctx.buf op.impl i := by
  have hsim := hop.sim
  have hib := hop.ib
  have hri := ctx.sim.repr.operations_indices op.spec hib
  have halt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op.spec hib
  have hsize : ctx.buf.mem.size < 2^63 := by grind
  have hinb := ctx.sim.in_bounds (.operation op.spec) (by grind)
  have hoib := OperationPtr.getResult_veir_inBounds op hop i h₂
  have haop := Sim.OpResultPtr.after_lt_ctx (ctx := ctx) (op.spec.getResult i.toNat) hoib
  have hplus : (Buffed.OperationMPtr.computeResultOffset! ctx.buf op.impl i).toInt
      = Buffed.Operation.Offsets.resultsInt op.spec ctx.spec + Buffed.OpResult.sizeNat * i.toNat := by
    simp only [Buffed.OperationMPtr.computeResultOffset!]
    rw [Int64.add_toInt_lt'] <;>
      grind [layout_grind, UInt64.toNat_mul, OperationPtr.computeResultsOffset!_ideal]
  have haddr : ((op.impl + Buffed.OperationMPtr.computeResultOffset! ctx.buf op.impl i).toNat : Int)
      = op.impl.toNat + (Buffed.Operation.Offsets.resultsInt op.spec ctx.spec + Buffed.OpResult.sizeNat * i.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
  rw [← UInt64.toNat_inj]
  have hflat := Veir.OpResultPtr.toFlat_ideal (ctx := ctx.spec) (by grind) (op.spec.getResult i.toNat) hoib
  simp only [Veir.OpResultPtr.toM, hflat]
  grind [layout_grind, Veir.OperationPtr.getResult_def, Nat.toUInt64_eq, UInt64.toNat_ofNat']

@[grind .]
theorem OperationPtr.getResult_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i.toNat < op.spec.getNumResults! ctx.spec) :
    (op.getResultPtr ctx i hop).InBounds ctx := by
  rw [Sim.OperationPtr.getResultPtr_eq_getResultPtr!]
  exact ⟨OperationPtr.getResult_toM op hop i h₂, OperationPtr.getResult_veir_inBounds op hop i h₂⟩

@[grind =>]
theorem OperationPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr)
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .fromOperation ptr') := by
  have hspec := Sim.OperationPtr.allocEmpty_spec' heq
  have hlay := Veir.OperationPtr.allocEmptyAt_preservesLayout hspec
  have hptr := Veir.OperationPtr.allocEmptyAt_ptr_eq hspec
  constructor
  · rintro ⟨sim', ib'⟩
    rcases (Veir.OperationPtr.allocEmptyAt_genericPtr_iff ptr.spec hspec).mp ib' with hold | hnew
    · -- Old pointer: the layout is preserved, so the address is unchanged.
      refine .inl ⟨?_, hold⟩
      have := Veir.GenericPtr.layoutPreserved_same_toM hlay hold
      grind [Sim.GenericPtr.Sim]
    · -- The freshly allocated operation: its impl address is forced by the sim relation.
      refine .inr ?_
      obtain ⟨impl, spec⟩ := ptr
      grind [Sim.GenericPtr.Sim, Sim.GenericPtr.fromOperation, Veir.GenericPtr.toM,
        Veir.OperationPtr.toM]
  · rintro (hold | rfl)
    · exact ⟨Sim.GenericPtr.sim_layoutPreserved hlay hold,
        (Veir.OperationPtr.allocEmptyAt_genericPtr_iff ptr.spec hspec).mpr (.inl hold.ib)⟩
    · refine ⟨?_, (Veir.OperationPtr.allocEmptyAt_genericPtr_iff _ hspec).mpr (.inr (by grind [Sim.GenericPtr.fromOperation]))⟩
      grind [Sim.GenericPtr.Sim, Sim.GenericPtr.fromOperation, Veir.GenericPtr.toM, Veir.OperationPtr.toM]

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
  have := (OperationPtr.allocEmpty_genericPtr_iff (.fromOperation ptr') heq).mpr (.inr rfl)
  grind [generic_ptr_grind]

@[grind .]
theorem OperationPtr.allocEmpty_newBlock_veir_inBounds {ptr : Veir.GenericPtr}
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  have hspec := Sim.OperationPtr.allocEmpty_spec' heq
  grind

@[grind .]
theorem OperationPtr.allocEmpty_not_inBounds
    (heq : allocEmpty ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ¬ ptr'.spec.InBounds ctx.spec :=
  Veir.OperationPtr.allocEmptyAt_not_inBounds (Sim.OperationPtr.allocEmpty_spec' heq)


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

/-- The spec-level block argument pointer is in bounds when its index is below the count. -/
theorem BlockPtr.getArgument_veir_inBounds (block : BlockPtr)
    (hblock : block.InBounds ctx) (i : UInt64) (h₂ : i.toNat < block.spec.getNumArguments ctx.spec) :
    (block.spec.getArgument i.toNat).InBounds ctx.spec := by
  have hib := hblock.ib
  grind [Veir.BlockPtr.getArgument_def, Veir.BlockArgumentPtr.inBounds_def]

/-- The buffer-side argument address computed by `getArgumentPtr!` is exactly the buffed address of the spec-level pointer `block.spec.getArgument i`. -/
theorem BlockPtr.getArgument_toM (block : BlockPtr)
    (hblock : block.InBounds ctx) (i : UInt64) (h₂ : i.toNat < block.spec.getNumArguments ctx.spec) :
    (block.spec.getArgument i.toNat).toM
      = block.impl + Buffed.BlockMPtr.computeArgumentOffset! i := by
  have hsim := hblock.sim
  have hib := hblock.ib
  have hri := ctx.sim.repr.blocks_indices block.spec hib
  have halt := Sim.BlockPtr.after_lt_ctx (ctx := ctx) block.spec hib
  have hsize : ctx.buf.mem.size < 2^63 := by grind
  have hoib := BlockPtr.getArgument_veir_inBounds block hblock i h₂
  have haop := Sim.BlockArgumentPtr.after_lt_ctx (ctx := ctx) (block.spec.getArgument i.toNat) hoib
  have hplus : (Buffed.BlockMPtr.computeArgumentOffset! i).toInt
      = Buffed.Block.Offsets.argumentsInt + Buffed.BlockArgument.sizeNat * i.toNat := by
    rw [← Buffed.BlockMPtr.computeArgumentOffset_eq_computeArgumentOffset!]
    exact BlockPtr.computeArgumentOffset_ideal ctx block i hib (by grind)
  have haddr : ((block.impl + Buffed.BlockMPtr.computeArgumentOffset! i).toNat : Int)
      = block.impl.toNat + (Buffed.Block.Offsets.argumentsInt + Buffed.BlockArgument.sizeNat * i.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
  rw [← UInt64.toNat_inj]
  have hflat := Veir.BlockArgumentPtr.toFlat_ideal (block.spec.getArgument i.toNat)
  simp only [Veir.BlockArgumentPtr.toM, hflat]
  grind [layout_grind, Veir.BlockPtr.getArgument_def, Nat.toUInt64_eq, UInt64.toNat_ofNat']

@[grind .]
theorem BlockPtr.getArgument_inBounds (block : BlockPtr)
    (hblock : block.InBounds ctx) i (h₂ : i.toNat < block.spec.getNumArguments ctx.spec) :
    (block.getArgumentPtr ctx i hblock).InBounds ctx := by
  rw [Sim.BlockPtr.getArgumentPtr_eq_getArgumentPtr!]
  exact ⟨BlockPtr.getArgument_toM block hblock i h₂, BlockPtr.getArgument_veir_inBounds block hblock i h₂⟩

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
  have hspec := Sim.BlockPtr.allocEmpty_spec' numArgs heq
  have hlay := Veir.BlockPtr.allocEmptyAtAddress_preservesLayout hspec
  have hptr := Veir.BlockPtr.allocEmptyAtAddress_ptr hspec
  have hnew : ptr'.InBounds ctx' := by
    have hib := (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block ptr'.spec) hspec).mpr
      (.inr (.inl rfl))
    refine ⟨?_, by grind⟩
    grind [Sim.BlockPtr.Sim, Veir.BlockPtr.toM]
  have hslot := Sim.BlockPtr.getOpOperandPtrPtr_sim_of_sim (ctx := ctx') ptr' hnew
  constructor
  · rintro ⟨sim', ib'⟩
    rcases (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff ptr.spec hspec).mp ib' with hold | hb | hfu
    · -- Old pointer: the layout is preserved, so the address is unchanged.
      refine .inl ⟨?_, hold⟩
      have := Veir.GenericPtr.layoutPreserved_same_toM hlay hold
      grind [Sim.GenericPtr.Sim]
    · -- The freshly allocated block: its impl address is forced by the sim relation.
      refine .inr (.inl ?_)
      obtain ⟨impl, spec⟩ := ptr
      grind [Sim.GenericPtr.Sim, Sim.GenericPtr.fromBlock, Veir.GenericPtr.toM, Veir.BlockPtr.toM]
    · -- The new block's `firstUse` slot: its impl address is forced by the sim relation.
      refine .inr (.inr ?_)
      obtain ⟨impl, spec⟩ := ptr
      grind [Sim.GenericPtr.Sim, Sim.GenericPtr.fromBlockOperandPtr, Veir.GenericPtr.toM,
        Sim.BlockPtr.getBlockOperandPtrPtr, Sim.BlockOperandPtrPtr.Sim]
  · rintro (hold | rfl | rfl)
    · exact ⟨Sim.GenericPtr.sim_layoutPreserved hlay hold,
        (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff ptr.spec hspec).mpr (.inl hold.ib)⟩
    · refine ⟨?_, (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff _ hspec).mpr
        (.inr (.inl (by grind [Sim.GenericPtr.fromBlock])))⟩
      grind [Sim.GenericPtr.Sim, Sim.GenericPtr.fromBlock, Veir.GenericPtr.toM, Sim.BlockPtr.Sim]
    · refine ⟨?_, (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff _ hspec).mpr
        (.inr (.inr (by grind [Sim.GenericPtr.fromBlockOperandPtr, Sim.BlockPtr.getBlockOperandPtrPtr])))⟩
      grind [Sim.GenericPtr.Sim, Sim.GenericPtr.fromBlockOperandPtr, Veir.GenericPtr.toM,
        Sim.BlockPtr.getBlockOperandPtrPtr, Sim.BlockOperandPtrPtr.Sim]

@[grind .]
theorem BlockPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr) (heq : allocEmpty ctx numArgs = some (ptr', ctx')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem BlockPtr.allocEmpty_genericPtr_veir_mono (ptr : Veir.GenericPtr) (heq : allocEmpty ctx numArgs = some (ptr', ctx')) :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  have hspec := Sim.BlockPtr.allocEmpty_spec' numArgs heq
  grind

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

@[grind =>]
theorem RegionPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr) (heq : allocEmpty ctx = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .fromRegion ptr') := by
  have hspec := Sim.RegionPtr.allocEmpty_spec' heq
  have hlay := (Veir.RegionPtr.allocEmptyAt_preservesLayout hspec).preserves
  have hptr := Veir.RegionPtr.allocEmptyAt_ptr hspec
  constructor
  · rintro ⟨sim', ib'⟩
    rcases (Veir.RegionPtr.allocEmptyAt_genericPtr_iff ptr.spec hspec).mp ib' with hold | hnew
    · -- Old pointer: the layout is preserved, so the address is unchanged.
      refine .inl ⟨?_, hold⟩
      have := Veir.GenericPtr.layoutPreserved_same_toM hlay hold
      grind [Sim.GenericPtr.Sim]
    · -- The freshly allocated region: its impl address is forced by the sim relation.
      refine .inr ?_
      obtain ⟨impl, spec⟩ := ptr
      grind [Sim.GenericPtr.Sim, Sim.GenericPtr.fromRegion, Veir.GenericPtr.toM,
        Veir.RegionPtr.toM]
  · rintro (hold | rfl)
    · exact ⟨Sim.GenericPtr.sim_layoutPreserved hlay hold,
        (Veir.RegionPtr.allocEmptyAt_genericPtr_iff ptr.spec hspec).mpr (.inl hold.ib)⟩
    · refine ⟨?_, (Veir.RegionPtr.allocEmptyAt_genericPtr_iff _ hspec).mpr
        (.inr (by grind [Sim.GenericPtr.fromRegion]))⟩
      grind [Sim.GenericPtr.Sim, Sim.GenericPtr.fromRegion, Veir.GenericPtr.toM,
        Veir.RegionPtr.toM]

@[grind .]
theorem RegionPtr.allocEmpty_newBlock_inBounds (heq : allocEmpty ctx = some (ptr, ctx')) :
    ptr.InBounds ctx' :=
  (Sim.GenericPtr.iff_region ptr).mp
    ((RegionPtr.allocEmpty_genericPtr_iff (.fromRegion ptr) heq).mpr (.inr rfl))

@[grind .]
theorem RegionPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr) (heq : allocEmpty ctx = some (ptr', ctx')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem RegionPtr.allocEmpty_genericPtr_veir_mono (ptr : Veir.GenericPtr) (heq : allocEmpty ctx = some (ptr', ctx')) :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  have hspec := Sim.RegionPtr.allocEmpty_spec' heq
  grind

@[grind .]
theorem RegionPtr.allocEmpty_not_inBounds (heq : allocEmpty ctx = some (ptr', ctx')) :
    ¬ ptr'.spec.InBounds ctx.spec :=
  Veir.RegionPtr.allocEmptyAt_newBlock_not_inBounds (Sim.RegionPtr.allocEmpty_spec' heq)

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
