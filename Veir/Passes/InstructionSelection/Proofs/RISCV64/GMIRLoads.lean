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
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree
attribute [local implicit_reducible] TypeAttr

theorem intLoad_riscvLoad (memory : MemoryState) (p : Data.Pointer)
    (bytes : Nat) (hw : 8 * bytes ≤ 64) (value : Data.LLVM.Int (8 * bytes))
    (h : memory.intLoad p (8 * bytes) = .ok value) (ext : LoadExtension) :
    ∃ bits : BitVec 64, riscvLoad memory p.address.toBitVec bytes ext = .ok (bits, memory) ∧
      value ⊒ Data.LLVM.Int.val (bits.setWidth (8 * bytes)) := by
  unfold MemoryState.intLoad at h
  split at h
  · contradiction
  simp only [MemoryState.loadByte, Nat.mul_mod_right, ne_eq, not_true_eq_false,
    ↓reduceIte, Nat.mul_div_right _ (by veir_bv_decide : 0 < 8), Interp.bind_ok] at h
  cases hp : memory.loadPoison p bytes.toUInt64 <;>
    simp -failIfUnchanged only [hp, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i poison
  cases hl : memory.load p bytes.toUInt64 <;>
    simp only [hl, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i data
  simp only [Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq] at h
  subst value
  refine ⟨(match ext with
      | .signExt => (data.toBitVecLE (8 * bytes)).signExtend 64
      | .zeroExt => (data.toBitVecLE (8 * bytes)).setWidth 64), ?_, ?_⟩
  · simp [riscvLoad, MemoryState.decode, hl]
    rfl
  · simp [Data.LLVM.Byte.toInt]
    split <;> simp_all [isRefinedBy]
    cases ext <;> simp [BitVec.setWidth_setWidth_of_le _ hw]
    ext i hi
    simp [BitVec.getElem_signExtend, hi, Nat.lt_of_lt_of_le hi hw]


/-- The target memory read and result cast shared by all GMIR load addressing modes. -/
def gmirLoad_target (memory : MemoryState) (address : BitVec 64) (resultType : TypeAttr)
    (bytes : Nat) (ext : LoadExtension) :
    Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  let (bits, memory) ← monadLift (riscvLoad memory address bytes ext)
  let result ← Builtin.interpretUnrealizedConversionCastCTree #[resultType]
    #[RuntimeValue.reg ⟨bits⟩] memory
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
      | exact intLoad_riscvLoad memory p 1 (by veir_bv_decide) value hl ext
      | exact intLoad_riscvLoad memory p 2 (by veir_bv_decide) value hl ext
      | exact intLoad_riscvLoad memory p 4 (by veir_bv_decide) value hl ext
      | exact intLoad_riscvLoad memory p 8 (by veir_bv_decide) value hl ext)
    simp [gmirLoad_target, hload, ctree_semantics, ←Attribute.integerType_eq_of,
      Builtin.interpretUnrealizedConversionCastCTree, Functor.map, Bind.bind]
    cases value <;> simp_all [ctree_semantics, isRefinedBy]
    all_goals simp [CTree.tau_def, Sim.pure_tau, ctree_semantics, RISCV.Reg.toInt,
      Data.LLVM.Int.zext, Data.LLVM.Int.trunc, Data.LLVM.Int.ext, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals refine ⟨loadHighBits bits, ?_⟩
    all_goals simp [Id.run, isRefinedBy, loadHighBits]
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
  obtain ⟨bits, hload, href⟩ := llvmLoad_pointer_riscvLoad memory p ptr value hl
  have hext : riscvLoad memory p.address.toBitVec 8 ext = riscvLoad memory p.address.toBitVec 8 .zeroExt := by
    cases ext <;> simp [riscvLoad]
  rw [←hext] at hload
  cases value <;> simp [RuntimeValue.isRefinedBy] at href
  simp [gmirLoad_target, hload, ctree_semantics, Builtin.interpretUnrealizedConversionCastCTree,
    ←Attribute.llvmPointerType_eq_of, Bind.bind]
  exact href

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

private theorem gmirLoad_target_expanded (memory : MemoryState) (address : BitVec 64) (resultType : TypeAttr) (bytes : Nat) (ext : LoadExtension) :
    CTree.bind (monadLift do
        let v ← riscvLoad memory address bytes ext
        Interp.ok (#[RuntimeValue.reg ⟨v.1⟩],v.2,(none : Option ControlFlowAction)))
      (fun r => CTree.bind (Builtin.interpretUnrealizedConversionCastCTree #[resultType] #[r.1[0]!] r.2.1)
        (fun r => pure (#[r.1[0]!],r.2.1,none))) = gmirLoad_target memory address resultType bytes ext := by
  cases h : riscvLoad memory address bytes ext <;> simp [gmirLoad_target,h,monadLift,MonadLift.monadLift,Bind.bind]


theorem gmirLoad_reg_lbu_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .reg 1 .lbu) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg hc resultType props hv hlegal hsize memory
  obtain ⟨_, p, hp, rfl⟩ := isLegal_g_load_types resultType argType props hlegal
  simp only [RuntimeValue.Conforms.llvmPointerType] at hc
  rcases hc with ⟨pointer,rfl⟩
  cases pointer with
  | poison => simp [ctree_semantics, Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
    simp [ctree_semantics, Data.LLVM.Ptr.toInt]
    intro reg hr
    have hs := gmirLoad_sim memory p resultType (TypeAttr.of LLVM.PointerType _) props 1
      (by simp) hlegal hsize .zeroExt
    simp [gmirLoad_target, ctree_semantics, hr, riscvEffectiveAddr, RISCVMemProperties.imm12]
    rw [gmirLoad_target_expanded]
    exact hs

theorem gmirLoad_reg_lh_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .reg 2 .lh) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg hc resultType props hv hlegal hsize memory
  obtain ⟨_, p, hp, rfl⟩ := isLegal_g_load_types resultType argType props hlegal
  simp only [RuntimeValue.Conforms.llvmPointerType] at hc
  rcases hc with ⟨pointer,rfl⟩
  cases pointer with
  | poison => simp [ctree_semantics, Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
    simp [ctree_semantics, Data.LLVM.Ptr.toInt]
    intro reg hr
    have hs := gmirLoad_sim memory p resultType (TypeAttr.of LLVM.PointerType _) props 2
      (by simp) hlegal hsize .signExt
    simp [gmirLoad_target, ctree_semantics, hr, riscvEffectiveAddr, RISCVMemProperties.imm12]
    rw [gmirLoad_target_expanded]
    exact hs

theorem gmirLoad_reg_lw_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .reg 4 .lw) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg hc resultType props hv hlegal hsize memory
  obtain ⟨_, p, hp, rfl⟩ := isLegal_g_load_types resultType argType props hlegal
  simp only [RuntimeValue.Conforms.llvmPointerType] at hc
  rcases hc with ⟨pointer,rfl⟩
  cases pointer with
  | poison => simp [ctree_semantics, Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
    simp [ctree_semantics, Data.LLVM.Ptr.toInt]
    intro reg hr
    have hs := gmirLoad_sim memory p resultType (TypeAttr.of LLVM.PointerType _) props 4
      (by simp) hlegal hsize .signExt
    simp [gmirLoad_target, ctree_semantics, hr, riscvEffectiveAddr, RISCVMemProperties.imm12]
    rw [gmirLoad_target_expanded]
    exact hs

theorem gmirLoad_reg_ld_valid :
    Puddle.CTree.Pattern.Valid (gmirLoad_pattern .reg 8 .ld) := by
  dsimp only [gmirLoad_pattern, lowerLoadOf, matchAddr, addrMemProps, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro argType arg hc resultType props hv hlegal hsize memory
  obtain ⟨_, p, hp, rfl⟩ := isLegal_g_load_types resultType argType props hlegal
  simp only [RuntimeValue.Conforms.llvmPointerType] at hc
  rcases hc with ⟨pointer,rfl⟩
  cases pointer with
  | poison => simp [ctree_semantics, Bind.bind, monadLift, MonadLift.monadLift]
  | val p =>
    simp [ctree_semantics, Data.LLVM.Ptr.toInt]
    intro reg hr
    have hs := gmirLoad_sim memory p resultType (TypeAttr.of LLVM.PointerType _) props 8
      (by simp) hlegal hsize .zeroExt
    simp [gmirLoad_target, ctree_semantics, hr, riscvEffectiveAddr, RISCVMemProperties.imm12]
    rw [gmirLoad_target_expanded]
    exact hs

end Veir
