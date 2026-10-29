module

public import Veir.Interfaces.FoldInterfaces.Soundness
public import Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.FoldDecision
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Interpreter.Refinement.Basic
import Veir.Data.RISCV.Reg.Lemmas

/-!
# Soundness of the RISC-V fold table

Every entry of `Riscv.tryFold` is proved against `Riscv.interpretOp'`. Registers
carry no poison, so each entry reduces to an equation between 64-bit vectors,
which `bv_decide` checks.
-/

public section

namespace Veir
open Data

/-- The remainder by `-1`, which `bv_decide` does not reach at this width. -/
private theorem srem_allOnes (x : BitVec 64) : x.srem 18446744073709551615#64 = 0#64 :=
  BitVec.srem_zero_of_dvd (by simp [BitVec.toInt])

/--
Prove one entry, once the operands are registers and the known ones are
substituted: take the entry's chain of alternatives apart, then check each
alternative's equation.
-/
local macro "riscv_fold_entry" : tactic => `(tactic| (
  repeat' ((try dsimp only) <;> first
    | apply FoldTable.orElse_sound
    | apply FoldTable.useOperandIf_sound
    | apply FoldTable.useConstantIf_sound
    | apply FoldTable.some_sound)
  -- Unfolding a shift to a `Nat` amount would take it out of `bv_decide`'s reach.
  all_goals simp [regZero, regOne, regNonzero, regAllOnes, regIntMin, regIntMax, regShamtZero,
    wordZero, wordOne, wordAllOnes, knownReg, FoldDecision.resolveAll, FoldDecision.resolve,
    OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy,
    ControlFlowAction.optionIsRefinedBy, RISCVImmediateProperties.immField, RISCV.val_inj,
    RISCV.addi, RISCV.xori, RISCV.ori, RISCV.andi, RISCV.slli, RISCV.srli, RISCV.srai,
    RISCV.rori, RISCV.sltiu, RISCV.mv, RISCV.add, RISCV.sub, RISCV.xor, RISCV.xnor, RISCV.or,
    RISCV.and, RISCV.mul, RISCV.max, RISCV.min, RISCV.maxu, RISCV.minu, RISCV.mulh, RISCV.mulhu,
    RISCV.mulhsu, RISCV.mulw, RISCV.div, RISCV.divu, RISCV.divw, RISCV.divuw, RISCV.rem,
    RISCV.remu, RISCV.remw, RISCV.remuw, RISCV.sll, RISCV.srl, RISCV.sra, RISCV.rol, RISCV.ror,
    RISCV.sllw, RISCV.srlw, RISCV.sraw, RISCV.rolw, RISCV.rorw, RISCV.slt, RISCV.sltu,
    RISCV.adduw, RISCV.sh1adduw, RISCV.sh2adduw, RISCV.sh3adduw, RISCV.sh1add, RISCV.sh2add,
    RISCV.sh3add, RISCV.andn, RISCV.orn, RISCV.bclr, RISCV.bset, RISCV.bext, RISCV.czeroeqz,
    RISCV.czeronez, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq', -BitVec.sshiftRight_eq']
  all_goals intros
  all_goals first
    -- Substitute known constants before bit-blasting, especially for signed division by one.
    | (rename_i h; solve | simp [h, srem_allOnes, BitVec.sdiv_one])
    | bv_decide
    | (rename_i h; rcases h with h | h <;> simp [h, srem_allOnes])))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/--
The RISC-V fold table is sound: whenever it decides that an operation folds,
the decisions resolve, against any operands that agree with the known ones, to
the results of interpreting the operation.
-/
theorem Riscv.tryFold_sound
    (hFold : Riscv.tryFold op properties resultTypes known = some decisions)
    (hAgree : FoldTable.Agrees known operands)
    (hInterp : Riscv.interpretOp' op properties resultTypes operands blockOperands mem =
      .ok results) :
    ∃ replacements, FoldDecision.resolveAll decisions operands = some replacements ∧
      OperationResult.isRefinedBy results (replacements, mem, none) := by
  unfold Riscv.tryFold at hFold
  split at hFold
  all_goals first
    | (simp at hFold; done)
    | (obtain ⟨a, rfl, hl⟩ := hAgree.single ‹_›
       simp only [Riscv.interpretOp'] at hInterp
       split at hInterp <;> simp at hInterp
       rename_i hs
       simp only [List.cons.injEq, and_true] at hs
       subst hs hInterp
       rcases hl with rfl | rfl <;> revert decisions <;> riscv_fold_entry)
    | (obtain ⟨a, b, rfl, hl, hr⟩ := hAgree.pair ‹_›
       simp only [Riscv.interpretOp'] at hInterp
       split at hInterp <;> simp at hInterp
       rename_i hs
       simp only [List.cons.injEq, and_true] at hs
       obtain ⟨rfl, rfl⟩ := hs
       subst hInterp
       rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> revert decisions <;>
         riscv_fold_entry)

end Veir
