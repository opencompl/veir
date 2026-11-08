module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.GMIRLoads
import all Veir.Interpreter.CTree
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryAddressLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.LoadLegality

namespace Veir
open Puddle
open _root_.CTree
attribute [local ctree_semantics]
  Riscv.interpretOpCTree
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree
attribute [local implicit_reducible] TypeAttr

theorem gmirLoad_gepConst_lbu_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .gepConst 1 .lbu) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, -UInt64.ofInt_add]
  intro argType arg harg gepType gep verifiedGEP address hinterp
    resultType props verified selected legal size memory
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
      simp [Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
      intro reg hreg
      have heffective : riscvEffectiveAddr reg.val
          ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
          addr.address.toBitVec := by
        dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
        rw [pointer_add_offset]
        simp [hreg, selectedOffset_signExtend gep #[] offset hcount hselect]
      rw [gmirLoad_target_expanded, heffective]
      exact gmirLoad_sim memory addr resultType argType props 1 (.inl rfl) legal size .zeroExt

theorem gmirLoad_gepConst_lh_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .gepConst 2 .lh) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, -UInt64.ofInt_add]
  intro argType arg harg gepType gep verifiedGEP address hinterp
    resultType props verified selected legal size memory
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
      simp [Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
      intro reg hreg
      have heffective : riscvEffectiveAddr reg.val
          ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
          addr.address.toBitVec := by
        dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
        rw [pointer_add_offset]
        simp [hreg, selectedOffset_signExtend gep #[] offset hcount hselect]
      rw [gmirLoad_target_expanded, heffective]
      exact gmirLoad_sim memory addr resultType argType props 2 (by simp) legal size .signExt

theorem gmirLoad_gepConst_lw_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .gepConst 4 .lw) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, -UInt64.ofInt_add]
  intro argType arg harg gepType gep verifiedGEP address hinterp
    resultType props verified selected legal size memory
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
      simp [Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
      intro reg hreg
      have heffective : riscvEffectiveAddr reg.val
          ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
          addr.address.toBitVec := by
        dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
        rw [pointer_add_offset]
        simp [hreg, selectedOffset_signExtend gep #[] offset hcount hselect]
      rw [gmirLoad_target_expanded, heffective]
      exact gmirLoad_sim memory addr resultType argType props 4 (by simp) legal size .signExt

theorem gmirLoad_gepConst_ld_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .gepConst 8 .ld) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, -UInt64.ofInt_add]
  intro argType arg harg gepType gep verifiedGEP address hinterp
    resultType props verified selected legal size memory
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
      simp [Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
      intro reg hreg
      have heffective : riscvEffectiveAddr reg.val
          ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
          addr.address.toBitVec := by
        dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
        rw [pointer_add_offset]
        simp [hreg, selectedOffset_signExtend gep #[] offset hcount hselect]
      rw [gmirLoad_target_expanded, heffective]
      exact gmirLoad_sim memory addr resultType argType props 8 (by simp) legal size .zeroExt

theorem gmirLoad_gepIndex_lbu_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .gepIndex 1 .lbu) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of, -UInt64.ofInt_add]
  intro argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address hinterp
    resultType props verified selected legal size memory
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
      simp [Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
      intro reg hreg
      have heffective : riscvEffectiveAddr reg.val
          ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
          addr.address.toBitVec := by
        dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
        rw [pointer_add_offset]
        simp [hreg, selectedOffset_signExtend gep #[index] offset hcount hselect]
      rw [gmirLoad_target_expanded, heffective]
      exact gmirLoad_sim memory addr resultType argType props 1 (by simp) legal size .zeroExt

theorem gmirLoad_gepIndex_lh_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .gepIndex 2 .lh) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of, -UInt64.ofInt_add]
  intro argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address hinterp
    resultType props verified selected legal size memory
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
      simp [Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
      intro reg hreg
      have heffective : riscvEffectiveAddr reg.val
          ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
          addr.address.toBitVec := by
        dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
        rw [pointer_add_offset]
        simp [hreg, selectedOffset_signExtend gep #[index] offset hcount hselect]
      rw [gmirLoad_target_expanded, heffective]
      exact gmirLoad_sim memory addr resultType argType props 2 (by simp) legal size .signExt

theorem gmirLoad_gepIndex_lw_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .gepIndex 4 .lw) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of, -UInt64.ofInt_add]
  intro argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address hinterp
    resultType props verified selected legal size memory
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
      simp [Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
      intro reg hreg
      have heffective : riscvEffectiveAddr reg.val
          ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
          addr.address.toBitVec := by
        dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
        rw [pointer_add_offset]
        simp [hreg, selectedOffset_signExtend gep #[index] offset hcount hselect]
      rw [gmirLoad_target_expanded, heffective]
      exact gmirLoad_sim memory addr resultType argType props 4 (by simp) legal size .signExt

theorem gmirLoad_gepIndex_ld_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .gepIndex 8 .ld) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of, -UInt64.ofInt_add]
  intro argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address hinterp
    resultType props verified selected legal size memory
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
      simp [Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp memory
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] memory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt]
      intro reg hreg
      have heffective : riscvEffectiveAddr reg.val
          ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
          addr.address.toBitVec := by
        dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
        rw [pointer_add_offset]
        simp [hreg, selectedOffset_signExtend gep #[index] offset hcount hselect]
      rw [gmirLoad_target_expanded, heffective]
      exact gmirLoad_sim memory addr resultType argType props 8 (by simp) legal size .zeroExt

end Veir
