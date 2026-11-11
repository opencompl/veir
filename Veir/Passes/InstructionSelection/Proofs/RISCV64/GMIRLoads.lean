module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.LoadLegality
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Interpreter.Memory
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Data.Pointer.Basic
import all Veir.Passes.InstructionSelection.Proofs
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Int.Basic
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.LegalizerInfo

namespace Veir
open Puddle
open _root_.CTree
attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree Riscv.interpretOpCTree
attribute [local implicit_reducible] TypeAttr

theorem intLoad_riscvLoadCTree (memory : MemoryState) (p : Data.Pointer)
    (bytes : Nat) (hw : 8 * bytes ≤ 64) (value : Data.LLVM.Int (8 * bytes))
    (h : memory.intLoad p (8 * bytes) = .ok value) (ext : LoadExtension) :
    ∃ b : Data.LLVM.Byte (8 * bytes), memory.loadByte p (8 * bytes) = .ok b ∧
      ∀ choice, value ⊒ Data.LLVM.Int.val ((resolvedLoadBits b choice ext).setWidth (8 * bytes)) := by
  unfold MemoryState.intLoad at h
  split at h
  · contradiction
  cases hl : memory.loadByte p (8 * bytes) <;>
    simp [hl, Interp.pure_eq] at h
  rename_i b
  subst value
  refine ⟨b, rfl, ?_⟩
  intro choice
  by_cases hp : b.poison = 0#(8 * bytes)
  · cases ext <;> simp [Data.LLVM.Byte.toInt, hp, resolvedLoadBits, isRefinedBy,
      BitVec.setWidth_setWidth_of_le _ hw]
    ext i hi
    simp [BitVec.getElem_signExtend, hi, Nat.lt_of_lt_of_le hi hw]
  · simp [Data.LLVM.Byte.toInt, hp, isRefinedBy]


/-- The target memory read and result cast shared by all GMIR load addressing modes. -/
def gmirLoad_target (memory : MemoryState) (address : BitVec 64) (resultType : TypeAttr)
    (bytes : Nat) (ext : LoadExtension) :
    Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  let loaded ← riscvLoadCTree 0 #[RuntimeValue.reg ⟨address⟩] memory bytes ext
  let result ← Builtin.interpretUnrealizedConversionCastCTree #[resultType]
    #[loaded.1[0]!] loaded.2.1
  pure (#[result.1[0]!], result.2.1, none)

private def loadHighBits {n : Nat} (bits : BitVec 64) : BitVec n :=
  bits.extractLsb' (64 - n) n

theorem gmirLoad_integer_sim (memory : MemoryState) (p : Data.Pointer)
    (sign : IntegerType.Signedness) (props : MachineMemOperand) (bytes : Nat)
    (hbytes : bytes = 1 ∨ bytes = 2 ∨ bytes = 4 ∨ bytes = 8)
    (hsize : props.size.toNat = 8 * bytes) (ext : LoadExtension) :
    Sim (fun (target source : Array RuntimeValue × MemoryState × Option ControlFlowAction) => source.1 ⊒ target.1 ∧ source.2.1 ⊒ target.2.1 ∧
      ControlFlowAction.optionIsRefinedBy source.2.2 target.2.2)
      (gmirLoad_target memory p.address.toBitVec (TypeAttr.of IntegerType ⟨64,sign⟩) bytes ext)
      (GMIR.interpretOpCTree .g_load props #[TypeAttr.of IntegerType ⟨64,sign⟩]
        #[RuntimeValue.addr (.val p)] #[] memory) := by
  rcases props with ⟨size,alignment,volatile_,nontemporal,invariant⟩
  have hs : size = BitVec.ofNat 64 (8 * bytes) := by
    apply BitVec.eq_of_toNat_eq
    rcases hbytes with rfl | rfl | rfl | rfl <;> simpa using hsize
  subst size
  rcases hbytes with rfl | rfl | rfl | rfl
  all_goals
    simp only [GMIR.interpretOpCTree, GMIR.interpretOp', ←Attribute.integerType_eq_of]
    cases ha : p.checkAlignment alignment.toNat <;>
      simp [ha, monadLift, MonadLift.monadLift, Bind.bind, ctree_semantics, ←Attribute.integerType_eq_of]
    cases hl : memory.intLoad p _ <;>
      simp [hl, monadLift, MonadLift.monadLift, Bind.bind, ctree_semantics, ←Attribute.integerType_eq_of]
    rename_i value
    obtain ⟨bits,hload,href⟩ := (by
      first
      | exact intLoad_riscvLoadCTree memory p 1 (by veir_bv_decide) value hl ext
      | exact intLoad_riscvLoadCTree memory p 2 (by veir_bv_decide) value hl ext
      | exact intLoad_riscvLoadCTree memory p 4 (by veir_bv_decide) value hl ext
      | exact intLoad_riscvLoadCTree memory p 8 (by veir_bv_decide) value hl ext)
    simp [gmirLoad_target, riscvLoadCTree, riscvEffectiveAddr, MemoryState.decode, hload,
      ctree_semantics, ←Attribute.integerType_eq_of,
      Builtin.interpretUnrealizedConversionCastCTree, Functor.map, Bind.bind,
      CTree.choose_def, CTree.tau_def]
    intro choice
    change BitVec _ at choice
    specialize href choice
    let loadedBits := resolvedLoadBits bits choice ext
    cases value <;> simp_all [ctree_semantics, isRefinedBy]
    all_goals simp [CTree.tau_def, Sim.pure_tau, ctree_semantics, RISCV.Reg.toInt,
      Data.LLVM.Int.zext, Data.LLVM.Int.trunc, Data.LLVM.Int.ext, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals try refine ⟨loadHighBits loadedBits, ?_⟩
    all_goals cases ext <;> simp [Id.run, isRefinedBy, loadHighBits, loadedBits, resolvedLoadBits] at *
    all_goals veir_bv_decide

theorem gmirLoad_pointer_sim (memory : MemoryState) (p : Data.Pointer)
    (ptr : LLVM.PointerType) (props : MachineMemOperand) (ext : LoadExtension) :
    Sim (fun (target source : Array RuntimeValue × MemoryState × Option ControlFlowAction) =>
      source.1 ⊒ target.1 ∧ source.2.1 ⊒ target.2.1 ∧
      ControlFlowAction.optionIsRefinedBy source.2.2 target.2.2)
      (gmirLoad_target memory p.address.toBitVec (TypeAttr.of LLVM.PointerType ptr) 8 ext)
      (GMIR.interpretOpCTree .g_load props #[TypeAttr.of LLVM.PointerType ptr]
        #[RuntimeValue.addr (.val p)] #[] memory) := by
  simp only [GMIR.interpretOpCTree, GMIR.interpretOp', ←Attribute.llvmPointerType_eq_of]
  cases ha : p.checkAlignment props.alignment.toNat <;>
    simp [ha, monadLift, MonadLift.monadLift, Bind.bind, ctree_semantics,
      ←Attribute.llvmPointerType_eq_of]
  cases hl : memory.llvmLoad p (TypeAttr.of LLVM.PointerType ptr) <;>
    simp [hl, monadLift, MonadLift.monadLift, Bind.bind, ctree_semantics,
      ←Attribute.llvmPointerType_eq_of]
  rename_i value
  obtain ⟨bits, hload, href⟩ := llvmLoad_pointer_riscvLoadCTree memory p ptr value hl
  cases value <;> simp [RuntimeValue.isRefinedBy] at href
  simp [gmirLoad_target, riscvLoadCTree, riscvEffectiveAddr, MemoryState.decode, hload,
    ctree_semantics, Builtin.interpretUnrealizedConversionCastCTree,
    ←Attribute.llvmPointerType_eq_of, Functor.map, Bind.bind, CTree.choose_def, CTree.tau_def]
  cases ext <;> simpa [resolvedLoadBits, RuntimeValue.isRefinedBy, isRefinedBy] using href

theorem gmirLoad_sim (memory : MemoryState) (p : Data.Pointer)
    (resultType addrType : TypeAttr) (props : MachineMemOperand) (bytes : Nat)
    (hbytes : bytes = 1 ∨ bytes = 2 ∨ bytes = 4 ∨ bytes = 8)
    (hlegal : riscv64LegalizerInfo.isLegal .g_load #[resultType,addrType] props = true)
    (hsize : props.size.toNat = 8 * bytes) (ext : LoadExtension) :
    Sim (fun (target source : Array RuntimeValue × MemoryState × Option ControlFlowAction) =>
      source.1 ⊒ target.1 ∧ source.2.1 ⊒ target.2.1 ∧
      ControlFlowAction.optionIsRefinedBy source.2.2 target.2.2)
      (gmirLoad_target memory p.address.toBitVec resultType bytes ext)
      (GMIR.interpretOpCTree .g_load props #[resultType]
        #[RuntimeValue.addr (.val p)] #[] memory) := by
  obtain ⟨htypes, _⟩ := isLegal_g_load_types resultType addrType props hlegal
  rcases htypes with ⟨sign,rfl⟩ | ⟨ptr,hptr,rfl⟩
  · exact gmirLoad_integer_sim memory p sign props bytes hbytes hsize ext
  · have hs := isLegal_g_load_pointer_size ptr addrType props hlegal
    have hb : bytes = 8 := by
      rcases hbytes with rfl | rfl | rfl | rfl <;> simp_all
    subst bytes
    exact gmirLoad_pointer_sim memory p ptr props ext

theorem gmirLoad_target_expanded (memory : MemoryState) (reg : Data.RISCV.Reg)
    (imm : BitVec 12) (resultType : TypeAttr) (bytes : Nat) (ext : LoadExtension)
    (htypes : (∃ sign, resultType = TypeAttr.of IntegerType ⟨64, sign⟩) ∨
      ∃ p, p.addressSpace = 0 ∧ resultType = TypeAttr.of LLVM.PointerType p) :
    CTree.bind (riscvLoadCTree imm #[RuntimeValue.reg reg] memory bytes ext)
      (fun value => CTree.bind
        (if RuntimeValue.ArrayConforms value.1 #[TypeAttr.of RegisterType {}] then pure value else ub)
        (fun r => CTree.bind (Builtin.interpretUnrealizedConversionCastCTree #[resultType] #[r.1[0]!] r.2.1)
          (fun value => CTree.bind
            (if RuntimeValue.ArrayConforms value.1 #[TypeAttr.of TypeAttr resultType] then pure value else ub)
            (fun r => pure (#[r.1[0]!],r.2.1,none))))) =
      gmirLoad_target memory (riscvEffectiveAddr reg.val imm) resultType bytes ext := by
  rcases htypes with ⟨sign, rfl⟩ | ⟨p, _, rfl⟩
  all_goals cases ext <;>
    simp [gmirLoad_target, riscvLoadCTree, riscvEffectiveAddr, Bind.bind,
      CTree.bind_assoc_raw, Builtin.interpretUnrealizedConversionCastCTree,
      ←Attribute.integerType_eq_of, ←Attribute.llvmPointerType_eq_of]


theorem gmirLoad_reg_lbu_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .reg 1 .lbu) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg hc resultType props hv hlegal hsize memory
  obtain ⟨hresult, p, hp, rfl⟩ := isLegal_g_load_types resultType argType props hlegal
  simp only [RuntimeValue.Conforms.llvmPointerType] at hc
  rcases hc with ⟨pointer,rfl⟩
  cases pointer with
  | poison => simp [ctree_semantics, Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
    simp [ctree_semantics, Data.LLVM.Ptr.toInt]
    intro reg hr
    have hs := gmirLoad_sim memory p resultType (TypeAttr.of LLVM.PointerType _) props 1
      (by simp) hlegal hsize .zeroExt
    rw [gmirLoad_target_expanded _ _ _ _ _ _ hresult]
    simpa [hr, riscvEffectiveAddr, RISCVMemProperties.imm12,
      GMIR.interpretOpCTree, GMIR.interpretOp'] using hs

theorem gmirLoad_reg_lh_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .reg 2 .lh) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg hc resultType props hv hlegal hsize memory
  obtain ⟨hresult, p, hp, rfl⟩ := isLegal_g_load_types resultType argType props hlegal
  simp only [RuntimeValue.Conforms.llvmPointerType] at hc
  rcases hc with ⟨pointer,rfl⟩
  cases pointer with
  | poison => simp [ctree_semantics, Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
    simp [ctree_semantics, Data.LLVM.Ptr.toInt]
    intro reg hr
    have hs := gmirLoad_sim memory p resultType (TypeAttr.of LLVM.PointerType _) props 2
      (by simp) hlegal hsize .signExt
    rw [gmirLoad_target_expanded _ _ _ _ _ _ hresult]
    simpa [hr, riscvEffectiveAddr, RISCVMemProperties.imm12,
      GMIR.interpretOpCTree, GMIR.interpretOp'] using hs

theorem gmirLoad_reg_lw_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .reg 4 .lw) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg hc resultType props hv hlegal hsize memory
  obtain ⟨hresult, p, hp, rfl⟩ := isLegal_g_load_types resultType argType props hlegal
  simp only [RuntimeValue.Conforms.llvmPointerType] at hc
  rcases hc with ⟨pointer,rfl⟩
  cases pointer with
  | poison => simp [ctree_semantics, Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
    simp [ctree_semantics, Data.LLVM.Ptr.toInt]
    intro reg hr
    have hs := gmirLoad_sim memory p resultType (TypeAttr.of LLVM.PointerType _) props 4
      (by simp) hlegal hsize .signExt
    rw [gmirLoad_target_expanded _ _ _ _ _ _ hresult]
    simpa [hr, riscvEffectiveAddr, RISCVMemProperties.imm12,
      GMIR.interpretOpCTree, GMIR.interpretOp'] using hs

theorem gmirLoad_reg_ld_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .reg 8 .ld) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg hc resultType props hv hlegal hsize memory
  obtain ⟨hresult, p, hp, rfl⟩ := isLegal_g_load_types resultType argType props hlegal
  simp only [RuntimeValue.Conforms.llvmPointerType] at hc
  rcases hc with ⟨pointer,rfl⟩
  cases pointer with
  | poison => simp [ctree_semantics, Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
    simp [ctree_semantics, Data.LLVM.Ptr.toInt]
    intro reg hr
    have hs := gmirLoad_sim memory p resultType (TypeAttr.of LLVM.PointerType _) props 8
      (by simp) hlegal hsize .zeroExt
    rw [gmirLoad_target_expanded _ _ _ _ _ _ hresult]
    simpa [hr, riscvEffectiveAddr, RISCVMemProperties.imm12,
      GMIR.interpretOpCTree, GMIR.interpretOp'] using hs

end Veir
