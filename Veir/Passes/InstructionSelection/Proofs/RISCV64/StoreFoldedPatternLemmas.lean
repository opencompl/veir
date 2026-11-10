module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryAddressLemmas

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.StoreValueLemmas

namespace Veir

open Puddle
open _root_.CTree

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree
attribute [local implicit_reducible] TypeAttr

theorem lowerStore_gepConst_sb_of (store_refines : StorePrimitiveRefines 1) :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro ty width value conforms argType arg harg gepType gep verifiedGEP address hinterp
    props verified selected memory
  change ∀ memory, Llvm.interpretOp' .getelementptr gep #[gepType] #[arg] #[] memory
    .riscv64 = .ok (#[address], memory, none) at hinterp
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (have h := hinterp memory; simp [Llvm.interpretOp'] at h)
  rename_i pointer
  cases pointer with
  | poison =>
      have h := hinterp memory
      rw [show #[RuntimeValue.addr .poison] = #[.addr .poison] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[] offset #[gepType] memory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · simp only [RuntimeValue.Conforms.integerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType (IntegerType.signless 8))) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.int 8 x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of IntegerType ⟨8, sign⟩) (.int 8 x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
        rw [hs] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 1) href
      · contradiction

theorem lowerStore_gepConst_sh_of (store_refines : StorePrimitiveRefines 2) :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro ty width value conforms argType arg harg gepType gep verifiedGEP address hinterp
    props verified selected memory
  change ∀ memory, Llvm.interpretOp' .getelementptr gep #[gepType] #[arg] #[] memory
    .riscv64 = .ok (#[address], memory, none) at hinterp
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (have h := hinterp memory; simp [Llvm.interpretOp'] at h)
  rename_i pointer
  cases pointer with
  | poison =>
      have h := hinterp memory
      rw [show #[RuntimeValue.addr .poison] = #[.addr .poison] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[] offset #[gepType] memory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · simp only [RuntimeValue.Conforms.integerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType (IntegerType.signless 16))) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.int 16 x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of IntegerType ⟨16, sign⟩) (.int 16 x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
        rw [hs] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 2) href
      · contradiction

theorem lowerStore_gepConst_sw_of (store_refines : StorePrimitiveRefines 4) :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro ty width value conforms argType arg harg gepType gep verifiedGEP address hinterp
    props verified selected memory
  change ∀ memory, Llvm.interpretOp' .getelementptr gep #[gepType] #[arg] #[] memory
    .riscv64 = .ok (#[address], memory, none) at hinterp
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (have h := hinterp memory; simp [Llvm.interpretOp'] at h)
  rename_i pointer
  cases pointer with
  | poison =>
      have h := hinterp memory
      rw [show #[RuntimeValue.addr .poison] = #[.addr .poison] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[] offset #[gepType] memory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · simp only [RuntimeValue.Conforms.integerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType (IntegerType.signless 32))) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.int 32 x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of IntegerType ⟨32, sign⟩) (.int 32 x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
        rw [hs] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 4) href
      · contradiction

set_option maxHeartbeats 800000 in
theorem lowerStore_gepConst_sd_of (store_refines : StorePrimitiveRefines 8) :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro ty width value conforms argType arg harg gepType gep verifiedGEP address hinterp
    props verified selected memory
  change ∀ memory, Llvm.interpretOp' .getelementptr gep #[gepType] #[arg] #[] memory
    .riscv64 = .ok (#[address], memory, none) at hinterp
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (have h := hinterp memory; simp [Llvm.interpretOp'] at h)
  rename_i pointer
  cases pointer with
  | poison =>
      have h := hinterp memory
      rw [show #[RuntimeValue.addr .poison] = #[.addr .poison] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[] offset #[gepType] memory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · simp only [RuntimeValue.Conforms.integerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType (IntegerType.signless 64))) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.int 64 x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of IntegerType ⟨64, sign⟩) (.int 64 x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
        rw [hs] at href
        rw [store_fullWidth] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr (UInt64.ofBitVec rv.val).toByteArrayLE href
      · simp only [RuntimeValue.Conforms.llvmPointerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of LLVM.PointerType LLVM.PointerType.mk)) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.addr x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of LLVM.PointerType pointer) (.addr x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy, Data.LLVM.Ptr.toInt])
        rw [hs] at href
        rw [store_fullWidth] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr (UInt64.ofBitVec rv.val).toByteArrayLE href

theorem lowerStore_gepIndex_sb_of (store_refines : StorePrimitiveRefines 1) :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro ty width value conforms argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address hinterp
    props verified selected memory
  change ∀ memory, Llvm.interpretOp' .getelementptr gep #[gepType] #[arg, .int 64 (.val (BitVec.ofInt 64 index.value.value))] #[] memory
    .riscv64 = .ok (#[address], memory, none) at hinterp
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[index] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [List.size_toArray, List.length_cons, List.length_nil, Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (have h := hinterp memory; simp [Llvm.interpretOp'] at h)
  rename_i pointer
  cases pointer with
  | poison =>
      have h := hinterp memory
      rw [show #[RuntimeValue.addr .poison, .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr .poison] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[index] offset #[gepType] memory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · simp only [RuntimeValue.Conforms.integerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType (IntegerType.signless 8))) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.int 8 x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[index] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of IntegerType ⟨8, sign⟩) (.int 8 x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
        rw [hs] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 1) href
      · contradiction

theorem lowerStore_gepIndex_sh_of (store_refines : StorePrimitiveRefines 2) :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro ty width value conforms argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address hinterp
    props verified selected memory
  change ∀ memory, Llvm.interpretOp' .getelementptr gep #[gepType] #[arg, .int 64 (.val (BitVec.ofInt 64 index.value.value))] #[] memory
    .riscv64 = .ok (#[address], memory, none) at hinterp
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[index] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [List.size_toArray, List.length_cons, List.length_nil, Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (have h := hinterp memory; simp [Llvm.interpretOp'] at h)
  rename_i pointer
  cases pointer with
  | poison =>
      have h := hinterp memory
      rw [show #[RuntimeValue.addr .poison, .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr .poison] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[index] offset #[gepType] memory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · simp only [RuntimeValue.Conforms.integerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType (IntegerType.signless 16))) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.int 16 x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[index] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of IntegerType ⟨16, sign⟩) (.int 16 x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
        rw [hs] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 2) href
      · contradiction

theorem lowerStore_gepIndex_sw_of (store_refines : StorePrimitiveRefines 4) :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro ty width value conforms argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address hinterp
    props verified selected memory
  change ∀ memory, Llvm.interpretOp' .getelementptr gep #[gepType] #[arg, .int 64 (.val (BitVec.ofInt 64 index.value.value))] #[] memory
    .riscv64 = .ok (#[address], memory, none) at hinterp
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[index] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [List.size_toArray, List.length_cons, List.length_nil, Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (have h := hinterp memory; simp [Llvm.interpretOp'] at h)
  rename_i pointer
  cases pointer with
  | poison =>
      have h := hinterp memory
      rw [show #[RuntimeValue.addr .poison, .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr .poison] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[index] offset #[gepType] memory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · simp only [RuntimeValue.Conforms.integerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType (IntegerType.signless 32))) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.int 32 x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[index] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of IntegerType ⟨32, sign⟩) (.int 32 x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
        rw [hs] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 4) href
      · contradiction

set_option maxHeartbeats 800000 in
theorem lowerStore_gepIndex_sd_of (store_refines : StorePrimitiveRefines 8) :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro ty width value conforms argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address hinterp
    props verified selected memory
  change ∀ memory, Llvm.interpretOp' .getelementptr gep #[gepType] #[arg, .int 64 (.val (BitVec.ofInt 64 index.value.value))] #[] memory
    .riscv64 = .ok (#[address], memory, none) at hinterp
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[index] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [List.size_toArray, List.length_cons, List.length_nil, Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (have h := hinterp memory; simp [Llvm.interpretOp'] at h)
  rename_i pointer
  cases pointer with
  | poison =>
      have h := hinterp memory
      rw [show #[RuntimeValue.addr .poison, .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr .poison] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[index] offset #[gepType] memory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · simp only [RuntimeValue.Conforms.integerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType (IntegerType.signless 64))) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.int 64 x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[index] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of IntegerType ⟨64, sign⟩) (.int 64 x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
        rw [hs] at href
        rw [store_fullWidth] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr (UInt64.ofBitVec rv.val).toByteArrayLE href
      · simp only [RuntimeValue.Conforms.llvmPointerType] at conforms
        obtain ⟨x, rfl⟩ := conforms
        simp only [RuntimeValue.storedType]
        cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of LLVM.PointerType LLVM.PointerType.mk)) <;> simp [ha, ctree_semantics]
        cases hs : memory.llvmStore addr (.addr x) <;> simp [hs, ctree_semantics]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
        intro ra hra rv hrv
        have heffective : riscvEffectiveAddr ra.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hra, selectedOffset_signExtend gep #[index] offset hcount hselect]
        have href := store_refines memory addr (TypeAttr.of LLVM.PointerType pointer) (.addr x) rv width
          (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy, Data.LLVM.Ptr.toInt])
        rw [hs] at href
        rw [store_fullWidth] at href
        simpa [heffective, MemoryState.decode, OperationResult.isRefinedBy] using
          rawStore_sim memory _ addr (UInt64.ofBitVec rv.val).toByteArrayLE href

end Veir
