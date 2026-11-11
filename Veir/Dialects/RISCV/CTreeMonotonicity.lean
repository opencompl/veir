module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.RISCV.Monotonicity
public import Veir.Interpreter.CTreePrimitiveRefinement
public import Veir.Dialects.RISCV.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.RISCV.OpInfo
import Veir.Data.Casting
import Veir.Interpreter.Refinement.Memory

public section

/-!
# Monotonicity of the RISC-V opcodes in CTrees

Every RISC-V opcode but the loads runs its `Interp` semantics in CTrees, which is monotone in its
operands and its memory. A load chooses the bits of the loaded bytes that are poison. The source
reads the same address as the target, and from refined memory it reads bytes that the bytes of the
target refine, so it chooses the bits that give the register of the target.
-/

open CTree
open Veir.Data

namespace Veir.CTree

/-- A RISC-V opcode but a load runs its `Interp` semantics. -/
theorem interpretOp'_riscv {op : Riscv} (h : op.isLoad = false)
    (properties : propertiesOf (OpCode.riscv op)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr) :
    interpretOp' (.riscv op) properties resultTypes operands blockOperands mem regions =
      monadLift
        (Veir.interpretOp' (.riscv op) properties resultTypes operands blockOperands mem) := by
  rw [← Bool.not_eq_true, Riscv.isLoad_iff] at h
  cases op <;> simp at h <;> simp only [interpretOp', Riscv.interpretOpCTree,
    Veir.interpretOp', checkResultTypes_lift]

/-- A refinement in `Interp` together with what holds of every result of the target. -/
private theorem Interp.isRefinedBy_and {R : α → β → Prop} {P : β → Prop} {s : Interp α}
    {t : Interp β} (h : Interp.isRefinedBy R s t) (hP : ∀ b, t = .ok b → P b) :
    Interp.isRefinedBy (fun a b => R a b ∧ P b) s t := by
  cases s <;> cases t <;> simp_all [Interp.isRefinedBy]

/-- `riscvLoad` succeeds where the load of the bytes and their poison bits does. -/
private theorem riscvLoad_eq_ok_of_loadByte_eq_ok {mem : MemoryState} {eaddr : BitVec 64}
    {bytes : Nat} (ext : LoadExtension) {b : LLVM.Byte (8 * bytes)}
    (h : mem.loadByte (mem.decode (UInt64.ofBitVec eaddr)) (8 * bytes) = .ok b) :
    ∃ v, riscvLoad mem eaddr bytes ext = .ok (v, mem) := by
  obtain ⟨ba, hba⟩ := MemoryState.load_eq_ok_of_loadByte_eq_ok h
  rw [Nat.mul_div_cancel_left _ (by omega)] at hba
  simp [riscvLoad, hba]

/--
What holds of the values of the target, `Q`, and is the same for all registers: the types of the
values, or nothing.
-/
private def RegsAlike (Q : Array RuntimeValue → Prop) : Prop :=
  ∀ r r' : RISCV.Reg, Q #[.reg r] → Q #[.reg r']

/--
A RISC-V load is monotone in CTrees: from refined memory, the source loads bytes that the bytes of
the target refine, and chooses the bits that are poison so as to load the register of the target.
-/
private theorem sim_riscvLoadCTree {Q : Array RuntimeValue → Prop} (hQ : RegsAlike Q)
    (imm12 : BitVec 12) {operands operands' : Array RuntimeValue} {mem mem' : MemoryState}
    (bytes : Nat) (ext : LoadExtension) (h : operands ⊒ operands') (hMem : mem ⊒ mem')
    (hTyped : ∀ addr, operands'.toList = [.reg addr] → ∀ v m,
      riscvLoad mem' (riscvEffectiveAddr addr.val imm12) bytes ext = .ok (v, m) →
        Q #[.reg ⟨v⟩]) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ Q t.1)
      (riscvLoadCTree imm12 operands' mem' bytes ext : Tree _)
      (riscvLoadCTree imm12 operands mem bytes ext : Tree _) := by
  unfold riscvLoadCTree
  rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
  · simp
  rotate_left
  · simp
  obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
  cases v with
  | reg addr =>
    obtain rfl := RuntimeValue.reg_of_isRefinedBy hv
    have hT := hTyped addr hs'
    simp only [hs']
    rw [MemoryState.decode_eq_of_objects hMem.objects_eq]
    have hI := MemoryState.loadByte_isRefinedBy hMem
      (mem'.decode (UInt64.ofBitVec (riscvEffectiveAddr addr.val imm12))) (8 * bytes)
    generalize mem.loadByte _ _ = src at hI ⊢
    generalize htgt : mem'.loadByte _ _ = tgt at hI ⊢
    cases src with
    | ub _ =>
      simp only [monadLift, MonadLift.monadLift, tree_bind_eq, bind_ub]
      exact sim_ub _ _
    | fail _ =>
      simp only [monadLift, MonadLift.monadLift, tree_bind_eq, bind_fail]
      exact sim_fail _ _
    | ok b =>
      obtain ⟨b', rfl, hb⟩ := Interp.isRefinedBy_ok_target_iff.mp hI
      obtain ⟨v, hv⟩ := riscvLoad_eq_ok_of_loadByte_eq_ok ext htgt
      have hQ' := hT _ _ hv
      simp only [monadLift, MonadLift.monadLift, pure_bind]
      refine sim_choose_left _ fun bits => sim_choose_right _ (b'.val ||| (b'.poison &&& bits)) ?_
      rw [LLVM.Byte.resolve_of_isRefinedBy hb]
      exact (Sim.pure _ _ _).mpr ⟨OperationResult.isRefinedBy_def.mpr
        ⟨RuntimeValue.arrayIsRefinedBy_refl _, hMem, ControlFlowAction.optionIsRefinedBy_refl _⟩,
        hQ _ _ hQ'⟩
  | _ => simp

/-- Checked RISC-V execution preserves refinement and guarantees result conformance. -/
theorem riscv_sim_typed {op : Riscv} {opType : OpCode} (hType : opType = .riscv op)
    (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem') :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 resultTypes)
      (interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' opType properties resultTypes operands blockOperands mem regions) := by
  subst hType
  cases hLoad : op.isLoad
  · have := riscv_interpretOp'ContextuallyMonotone hLoad
    rw [interpretOp'_riscv hLoad, interpretOp'_riscv hLoad]
    apply sim_monadLift_of_isRefinedBy (Interp.isRefinedBy_and
      (this.monotone properties resultTypes operands operands' blockOperands mem mem' h hMem) ?_)
    rintro ⟨vals, m, a⟩ hok
    exact (Veir.checkResultTypes_ok_iff.mp hok).2
  · rw [interpretOp'_regions, interpretOp'_regions]
    rw [Riscv.isLoad_iff] at hLoad
    rcases hLoad with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [interpretOp', Riscv.interpretOpCTree] <;>
      apply sim_checkResultTypes <;>
      apply sim_mono (sim_riscvLoadCTree (Q := fun _ => True)
        (fun _ _ _ => trivial) _ _ _ h hMem (fun _ _ _ _ _ => trivial)) <;>
      exact fun _ _ h => h.1

/-- Every RISC-V opcode is monotone in CTrees. -/
theorem riscv_interpretOpTreeMonotone (op : Riscv) : InterpretOpTreeMonotone (.riscv op) where
  monotone properties resultTypes operands operands' blockOperands mem mem' regions h hMem :=
    sim_mono (riscv_sim_typed rfl properties resultTypes blockOperands regions h hMem)
      (fun _ _ h => h.1)

end Veir.CTree

namespace Veir

/--
Every RISC-V opcode is monotone in CTrees, with the results of the target typed: the obligation of
`OpCode.interpretCTree_monotone` holds for RISC-V. The types of the results come from
`OpCode.resultsConform_riscv`.
-/
theorem OpCode.interpretCTree_monotone_riscv (op : Riscv) :
    OpCode.interpretCTree_monotone (.riscv op) := by
  intro ctx o oIn hType hVerified sv tv sm tm hConf hRef hMem
  simp only [OperationPtr.interpretCTree]
  rw [OperationPtr.getResultTypes!_eq_getResultTypes oIn]
  exact CTree.riscv_sim_typed hType _ _ _ _ hRef hMem

/--
info: 'Veir.OpCode.interpretCTree_monotone_riscv' depends on axioms: [propext,
 Sim,
 Classical.choice,
 Quot.sound,
 Sim.bind,
 Sim.ret,
 Sim.tau_l,
 Sim.tau_r,
 Sim.ub]
-/
#guard_msgs in
#print axioms OpCode.interpretCTree_monotone_riscv

instance (op : Riscv) : InterpretCTreeMonotone (.riscv op) :=
  ⟨OpCode.interpretCTree_monotone_riscv op⟩

end Veir

end
