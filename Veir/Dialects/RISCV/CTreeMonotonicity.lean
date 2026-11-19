module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.RISCV.Monotonicity

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Memory
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.RISCV.OpInfo
import Veir.Data.LLVM.Byte.Lemmas
import Veir.Interpreter.Refinement.Memory

public section

/-!
# Monotonicity of the RISC-V opcodes in CTrees

Every RISC-V opcode but the loads runs its `Interp` semantics in CTrees, which is monotone in its
operands and its memory. A load chooses the bits of the loaded bytes that are poison. The source
reads the same address as the target, and from refined memory it reads bytes that the bytes of the
target refine, so it chooses the bits that give the register of the target. The types of the
results come from `ResultsConform`.
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
  cases op <;> simp at h <;> rfl

/-- A tree that returns a result may return it. -/
private theorem mayReturn_pure {α : Type} (r : α) : MayReturn (pure r : Tree α) r :=
  (MayReturn.pure_iff _ _).mpr rfl

/--
A RISC-V load is monotone in CTrees: from refined memory, the source loads bytes that the bytes of
the target refine, and chooses the bits that are poison so as to load the register of the target.
The result is of the types every result the target may return has.
-/
private theorem sim_riscvLoadCTree (imm12 : BitVec 12) {operands operands' : Array RuntimeValue}
    {mem mem' : MemoryState} (bytes : Nat) (ext : LoadExtension) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem') {types : Array TypeAttr}
    (hT : ∀ vals m a, MayReturn (riscvLoadCTree imm12 operands' mem' bytes ext : Tree _)
      (vals, m, a) → RuntimeValue.ArrayConforms vals types) :
    EqSim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 types)
      (riscvLoadCTree imm12 operands' mem' bytes ext : Tree _)
      (riscvLoadCTree imm12 operands mem bytes ext : Tree _) := by
  unfold riscvLoadCTree at hT ⊢
  rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
  · simp
  rotate_left
  · simp
  obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
  cases v with
  | reg addr =>
    obtain rfl := RuntimeValue.reg_of_isRefinedBy hv
    simp only [hs', MemoryState.decode] at hT ⊢
    have hI := MemoryState.loadByte_isRefinedBy hMem
      ⟨UInt64.ofBitVec (riscvEffectiveAddr addr.val imm12)⟩ (8 * bytes)
    generalize mem.loadByte _ _ = src at hI ⊢
    generalize mem'.loadByte _ _ = tgt at hI hT ⊢
    cases src with
    | ub _ =>
      simp only [monadLift, MonadLift.monadLift, tree_bind_eq, bind_ub]
      exact sim_ub _ _
    | fail _ =>
      simp only [monadLift, MonadLift.monadLift, tree_bind_eq, bind_fail]
      exact sim_fail _ _
    | ok b =>
      obtain ⟨b', rfl, hb⟩ := Interp.isRefinedBy_ok_target_iff.mp hI
      simp only [monadLift, MonadLift.monadLift, pure_bind] at hT ⊢
      refine sim_choose_left _ fun bits => sim_choose_right _ (b'.fillPoison bits) ?_
      rw [Data.LLVM.Byte.fillPoison_of_isRefinedBy hb]
      exact (EqSim.pure _ _ _).mpr ⟨OperationResult.isRefinedBy_def.mpr
        ⟨RuntimeValue.arrayIsRefinedBy_refl _, hMem, ControlFlowAction.optionIsRefinedBy_refl _⟩,
        hT _ _ _ (mayReturn_choose_bind bits (mayReturn_pure _))⟩
  | _ => simp

end Veir.CTree

namespace Veir

/--
Every RISC-V opcode whose results conform meets its CTree monotonicity obligation, the loads by
their own semantics.
-/
theorem OpCode.interpretCTree_monotone_riscv (op : Riscv) [Veir.ResultsConform (.riscv op)] :
    OpCode.interpretCTree_monotone (.riscv op) :=
  .of_sim fun properties resultTypes operands operands' blockOperands mem mem' regions h hMem
      hT => by
    cases hLoad : op.isLoad
    · have := riscv_interpretOp'Monotone hLoad
      exact CTree.sim_of_lift (fun _ _ => CTree.interpretOp'_riscv hLoad _ _ _ _ _ _) h hMem hT
    · rw [CTree.interpretOp'_regions, CTree.interpretOp'_regions] at hT ⊢
      rw [Riscv.isLoad_iff] at hLoad
      rcases hLoad with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [CTree.interpretOp', Riscv.interpretOpCTree] at hT ⊢ <;>
        exact CTree.sim_riscvLoadCTree _ _ _ h hMem hT

instance (op : Riscv) [ResultsConform (.riscv op)] : InterpretCTreeMonotone (.riscv op) :=
  ⟨OpCode.interpretCTree_monotone_riscv op⟩

end Veir

end
