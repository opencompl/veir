module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryAddressLemmas
import all Veir.Interpreter.Memory
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Data.Pointer.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Casting
import all Veir.ForLean

/-! Instruction-selection validity proofs for LLVM loads. -/

namespace Veir
open Puddle
open _root_.CTree
attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree Riscv.interpretOpCTree
attribute [local implicit_reducible] TypeAttr

theorem lowerLoad_reg_lbu_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .reg 1 .lbu) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg harg resultType props verified width memory
  obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
  · cases arg <;> simp [ctree_semantics]
    rename_i pointer
    cases pointer with
    | poison => simp
    | val p =>
        simp only [Data.LLVM.Ptr.toInt]
        cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨8, sign⟩)) <;>
          simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad p (TypeAttr.of IntegerType ⟨8, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad8_riscvLoadCTree memory p sign value hl .zeroExt
        simp [hr, riscvEffectiveAddr, RISCVMemProperties.imm12, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind,
          ←Attribute.integerType_eq_of, RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
  · contradiction

theorem lowerLoad_reg_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .reg 2 .lh) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg harg resultType props verified width memory
  obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
  · cases arg <;> simp [ctree_semantics]
    rename_i pointer
    cases pointer with
    | poison => simp
    | val p =>
        simp only [Data.LLVM.Ptr.toInt]
        cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨16, sign⟩)) <;>
          simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad p (TypeAttr.of IntegerType ⟨16, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad16_riscvLoadCTree memory p sign value hl .signExt
        simp [hr, riscvEffectiveAddr, RISCVMemProperties.imm12, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind,
          ←Attribute.integerType_eq_of, RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
  · contradiction

theorem lowerLoad_reg_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .reg 4 .lw) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg harg resultType props verified width memory
  obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
  · cases arg <;> simp [ctree_semantics]
    rename_i pointer
    cases pointer with
    | poison => simp
    | val p =>
        simp only [Data.LLVM.Ptr.toInt]
        cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨32, sign⟩)) <;>
          simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad p (TypeAttr.of IntegerType ⟨32, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad32_riscvLoadCTree memory p sign value hl .signExt
        simp [hr, riscvEffectiveAddr, RISCVMemProperties.imm12, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind,
          ←Attribute.integerType_eq_of, RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
  · contradiction

theorem lowerLoad_reg_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .reg 8 .ld) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg harg resultType props verified width memory
  obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
  · cases arg <;> simp [ctree_semantics]
    rename_i pointer
    cases pointer with
    | poison => simp
    | val p =>
        simp only [Data.LLVM.Ptr.toInt]
        cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨64, sign⟩)) <;>
          simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad p (TypeAttr.of IntegerType ⟨64, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad64_riscvLoadCTree memory p sign value hl .zeroExt
        simp [hr, riscvEffectiveAddr, RISCVMemProperties.imm12, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind,
          ←Attribute.integerType_eq_of, RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
  · cases arg <;> simp [ctree_semantics]
    rename_i address
    cases address with
    | poison => simp
    | val p =>
        simp only [Data.LLVM.Ptr.toInt]
        cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of LLVM.PointerType pointer)) <;>
          simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad p (TypeAttr.of LLVM.PointerType pointer) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad_pointer_riscvLoadCTree memory p pointer value hl
        simp [hreg, riscvEffectiveAddr, RISCVMemProperties.imm12, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind,
          ←Attribute.llvmPointerType_eq_of, RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href

theorem lowerLoad_gepConst_lbu_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .gepConst 1 .lbu) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg harg gepType gep verifiedGEP address _gepMemory _gepAfter hinterp
    resultType props verified selected width memory
  have hinterp : Llvm.interpretOp' .getelementptr gep #[gepType] #[arg] #[] _gepMemory
    .riscv64 = .ok (#[address], _gepAfter, none) := by
    simpa [Llvm.interpretOp'] using hinterp
  have hmemory := Llvm.interpretOp'_gep_memory _ _ _ _ _ _ _ _ _ hinterp
  subst _gepAfter
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (solve | have h := hinterp; simp [Llvm.interpretOp'] at h)
  rename_i pointer _
  cases pointer with
  | poison =>
      have h := hinterp
      rw [show #[RuntimeValue.addr .poison] = #[.addr .poison] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[] offset #[gepType] _gepMemory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] _gepMemory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨8, sign⟩)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of IntegerType ⟨8, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad8_riscvLoadCTree memory addr sign value hl .zeroExt
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.integerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
      · contradiction

theorem lowerLoad_gepConst_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .gepConst 2 .lh) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg harg gepType gep verifiedGEP address _gepMemory _gepAfter hinterp
    resultType props verified selected width memory
  have hinterp : Llvm.interpretOp' .getelementptr gep #[gepType] #[arg] #[] _gepMemory
    .riscv64 = .ok (#[address], _gepAfter, none) := by
    simpa [Llvm.interpretOp'] using hinterp
  have hmemory := Llvm.interpretOp'_gep_memory _ _ _ _ _ _ _ _ _ hinterp
  subst _gepAfter
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (solve | have h := hinterp; simp [Llvm.interpretOp'] at h)
  rename_i pointer _
  cases pointer with
  | poison =>
      have h := hinterp
      rw [show #[RuntimeValue.addr .poison] = #[.addr .poison] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[] offset #[gepType] _gepMemory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] _gepMemory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨16, sign⟩)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of IntegerType ⟨16, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad16_riscvLoadCTree memory addr sign value hl .signExt
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.integerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
      · contradiction

theorem lowerLoad_gepConst_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .gepConst 4 .lw) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg harg gepType gep verifiedGEP address _gepMemory _gepAfter hinterp
    resultType props verified selected width memory
  have hinterp : Llvm.interpretOp' .getelementptr gep #[gepType] #[arg] #[] _gepMemory
    .riscv64 = .ok (#[address], _gepAfter, none) := by
    simpa [Llvm.interpretOp'] using hinterp
  have hmemory := Llvm.interpretOp'_gep_memory _ _ _ _ _ _ _ _ _ hinterp
  subst _gepAfter
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (solve | have h := hinterp; simp [Llvm.interpretOp'] at h)
  rename_i pointer _
  cases pointer with
  | poison =>
      have h := hinterp
      rw [show #[RuntimeValue.addr .poison] = #[.addr .poison] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[] offset #[gepType] _gepMemory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] _gepMemory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨32, sign⟩)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of IntegerType ⟨32, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad32_riscvLoadCTree memory addr sign value hl .signExt
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.integerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
      · contradiction

theorem lowerLoad_gepConst_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .gepConst 8 .ld) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg harg gepType gep verifiedGEP address _gepMemory _gepAfter hinterp
    resultType props verified selected width memory
  have hinterp : Llvm.interpretOp' .getelementptr gep #[gepType] #[arg] #[] _gepMemory
    .riscv64 = .ok (#[address], _gepAfter, none) := by
    simpa [Llvm.interpretOp'] using hinterp
  have hmemory := Llvm.interpretOp'_gep_memory _ _ _ _ _ _ _ _ _ hinterp
  subst _gepAfter
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (solve | have h := hinterp; simp [Llvm.interpretOp'] at h)
  rename_i pointer _
  cases pointer with
  | poison =>
      have h := hinterp
      rw [show #[RuntimeValue.addr .poison] = #[.addr .poison] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[] offset #[gepType] _gepMemory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp
      rw [show #[RuntimeValue.addr (.val p)] = #[.addr (.val p)] ++ (#[] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[] offset #[gepType] _gepMemory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨64, sign⟩)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of IntegerType ⟨64, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad64_riscvLoadCTree memory addr sign value hl .zeroExt
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.integerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of LLVM.PointerType pointer)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of LLVM.PointerType pointer) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad_pointer_riscvLoadCTree memory addr pointer value hl
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.llvmPointerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href

theorem lowerLoad_gepIndex_lbu_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .gepIndex 1 .lbu) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address _gepMemory _gepAfter hinterp
    resultType props verified selected width memory
  have hinterp : Llvm.interpretOp' .getelementptr gep #[gepType] #[arg, .int 64 (.val (BitVec.ofInt 64 index.value.value))] #[] _gepMemory
    .riscv64 = .ok (#[address], _gepAfter, none) := by
    simpa [Llvm.interpretOp'] using hinterp
  have hmemory := Llvm.interpretOp'_gep_memory _ _ _ _ _ _ _ _ _ hinterp
  subst _gepAfter
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[index] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [List.size_toArray, List.length_cons, List.length_nil, Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (solve | have h := hinterp; simp [Llvm.interpretOp'] at h)
  rename_i pointer _
  cases pointer with
  | poison =>
      have h := hinterp
      rw [show #[RuntimeValue.addr .poison, .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr .poison] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[index] offset #[gepType] _gepMemory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] _gepMemory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨8, sign⟩)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of IntegerType ⟨8, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad8_riscvLoadCTree memory addr sign value hl .zeroExt
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[index] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.integerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
      · contradiction


theorem lowerLoad_gepIndex_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .gepIndex 2 .lh) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address _gepMemory _gepAfter hinterp
    resultType props verified selected width memory
  have hinterp : Llvm.interpretOp' .getelementptr gep #[gepType] #[arg, .int 64 (.val (BitVec.ofInt 64 index.value.value))] #[] _gepMemory
    .riscv64 = .ok (#[address], _gepAfter, none) := by
    simpa [Llvm.interpretOp'] using hinterp
  have hmemory := Llvm.interpretOp'_gep_memory _ _ _ _ _ _ _ _ _ hinterp
  subst _gepAfter
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[index] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [List.size_toArray, List.length_cons, List.length_nil, Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (solve | have h := hinterp; simp [Llvm.interpretOp'] at h)
  rename_i pointer _
  cases pointer with
  | poison =>
      have h := hinterp
      rw [show #[RuntimeValue.addr .poison, .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr .poison] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[index] offset #[gepType] _gepMemory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] _gepMemory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨16, sign⟩)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of IntegerType ⟨16, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad16_riscvLoadCTree memory addr sign value hl .signExt
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[index] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.integerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
      · contradiction


theorem lowerLoad_gepIndex_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .gepIndex 4 .lw) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address _gepMemory _gepAfter hinterp
    resultType props verified selected width memory
  have hinterp : Llvm.interpretOp' .getelementptr gep #[gepType] #[arg, .int 64 (.val (BitVec.ofInt 64 index.value.value))] #[] _gepMemory
    .riscv64 = .ok (#[address], _gepAfter, none) := by
    simpa [Llvm.interpretOp'] using hinterp
  have hmemory := Llvm.interpretOp'_gep_memory _ _ _ _ _ _ _ _ _ hinterp
  subst _gepAfter
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[index] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [List.size_toArray, List.length_cons, List.length_nil, Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (solve | have h := hinterp; simp [Llvm.interpretOp'] at h)
  rename_i pointer _
  cases pointer with
  | poison =>
      have h := hinterp
      rw [show #[RuntimeValue.addr .poison, .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr .poison] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[index] offset #[gepType] _gepMemory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] _gepMemory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨32, sign⟩)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of IntegerType ⟨32, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad32_riscvLoadCTree memory addr sign value hl .signExt
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[index] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.integerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
      · contradiction


theorem lowerLoad_gepIndex_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad .gepIndex 8 .ld) := by
  dsimp only [lowerLoad, lowerLoadOf, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro argType arg harg indexSign index verifiedIndex gepType gep verifiedGEP address _gepMemory _gepAfter hinterp
    resultType props verified selected width memory
  have hinterp : Llvm.interpretOp' .getelementptr gep #[gepType] #[arg, .int 64 (.val (BitVec.ofInt 64 index.value.value))] #[] _gepMemory
    .riscv64 = .ok (#[address], _gepAfter, none) := by
    simpa [Llvm.interpretOp'] using hinterp
  have hmemory := Llvm.interpretOp'_gep_memory _ _ _ _ _ _ _ _ _ hinterp
  subst _gepAfter
  obtain ⟨offset, hselect⟩ := Option.isSome_iff_exists.mp selected
  have hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ (#[index] : Array GMIRConstantProperties).size := by
    have := verifiedGEP.llvm_gep_dynamic_count
    simp only [List.size_toArray, List.length_cons, List.length_nil, Array.size_singleton, Array.size_empty] at this ⊢
    omega
  cases arg <;> try (solve | have h := hinterp; simp [Llvm.interpretOp'] at h)
  rename_i pointer _
  cases pointer with
  | poison =>
      have h := hinterp
      rw [show #[RuntimeValue.addr .poison, .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr .poison] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected_poison gep #[index] offset #[gepType] _gepMemory hcount hselect] at h
      have hv : address = .addr .poison := by simpa using h.symm
      subst address
      simp
  | val p =>
      let addr : Data.Pointer := ⟨UInt64.ofInt (p.address.toNat + offset)⟩
      have h := hinterp
      rw [show #[RuntimeValue.addr (.val p), .int 64 (.val (BitVec.ofInt 64 index.value.value))] = #[.addr (.val p)] ++ (#[index] : Array GMIRConstantProperties).map
        (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))) from by simp,
        interpretGEP_selected gep #[index] offset #[gepType] _gepMemory p hcount hselect] at h
      have hv : address = .addr (.val addr) := by simpa [addr] using h.symm
      subst address
      obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩) := memAccessWidth_cases width
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of IntegerType ⟨64, sign⟩)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of IntegerType ⟨64, sign⟩) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad64_riscvLoadCTree memory addr sign value hl .zeroExt
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[index] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.integerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href
      · cases ha : addr.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
            (Attribute.of LLVM.PointerType pointer)) <;> simp [ha, ctree_semantics]
        cases hl : memory.llvmLoad addr (TypeAttr.of LLVM.PointerType pointer) <;>
          simp [hl, ctree_semantics]
        rename_i value
        intro reg hreg
        have hr := hreg
        obtain ⟨bits, hload, href⟩ := llvmLoad_pointer_riscvLoadCTree memory addr pointer value hl
        have heffective : riscvEffectiveAddr reg.val
            ({ value := BitVec.ofInt 64 offset, volatile_ := props.volatile_ } : RISCVMemProperties).imm12 =
            addr.address.toBitVec := by
          dsimp only [riscvEffectiveAddr, RISCVMemProperties.imm12, addr]
          rw [pointer_add_offset]
          simp [hr, selectedOffset_signExtend gep #[index] offset hcount hselect]
        simp [hselect, ctree_semantics, Data.LLVM.Ptr.toInt] at hreg ⊢
        simp [heffective, hload, riscvLoadCTree, MemoryState.decode, ctree_semantics,
          Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind, ←Attribute.llvmPointerType_eq_of,
          RuntimeValue.arrayIsRefinedBy]
        simpa [resolvedLoadBits] using href


end Veir
