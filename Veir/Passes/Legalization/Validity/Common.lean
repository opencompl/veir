module

public import Veir.IR.Simp
public import Veir.IR.Attribute
import all Veir.PatternRewriter.Puddle.CTreeProofs
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.CombinerHelper
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Dialects.GMIR_RISCV.Semantics
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTreeInterpreter
import all Veir.IR.Attribute
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Validity
import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import Veir.Passes.Legalization.Proofs

/-! Shared imports and gMIR-specific tactics for the CTree validity proofs of the legalization
rules and the gMIR combines. Each proof file adds the interpreters to `ctree_semantics` and the gMIR
opcode metadata to `simp` with local attributes (see `Validity/Basic.lean`). Each proof normalizes the pattern's semantics down to a goal over
`Data.LLVM.Int` at symbolic widths, and closes it with the rule's local correctness lemma from
`Veir.Passes.Legalization.Proofs`. The generic machinery is in
`Veir.PatternRewriter.Puddle.CTreeProofs`. -/

/-- The `Status` of each legalization rule or gMIR combine, looked up by the coverage theorems of
`Veir.Passes.Legalization.Validity`. -/
register_simp_attr legalization_status

namespace Veir.Legalization.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree

public section

/-- Why a legalization rule or gMIR combine has no CTree validity proof. -/
inductive Unproven where
  /-- The rule is wrong at some widths: `g_bswap` is only defined at widths 16, 32 and 64, and
  other rules are wrong at the degenerate width 0, or from width `2^64`. -/
  | widthDependent
  /-- The rewrite drops a matched `g_anyext` and extends its operand again. The matched operation's
  high bits are fixed once it has run, and may reach its other uses, while the new `g_anyext`
  chooses them afresh, so the rewrite can produce values the source cannot. It is correct when the
  matched operation has no other use, which `Pattern.Valid` does not see. -/
  | rechoosesMatchedChoice
  /-- The local correctness lemma at every width is not proven yet. -/
  | notYetProven
  deriving Repr, DecidableEq

/-- A `g_constant` created at an integer type reads back the value it is created with. -/
theorem ofInt_ofInt_value (v : Int) (w : Nat) (s : IntegerType.Signedness) :
    BitVec.ofInt w (IntegerAttr.ofInt v ⟨w, s⟩).value = BitVec.ofInt w v := by
  simp only [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  split
  · rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [BitVec.ofInt_toInt]

end

open Lean Elab Tactic in
/-- Clear the hypotheses that each matched operation is verified (`IsFromVerifiedOp`), which the
proofs do not use: they would otherwise shift the positions of the hypotheses the proofs name,
and send `simp_all` into the existentials they hold. -/
elab "clearVerified" : tactic => do
  let goals ← getGoals
  setGoals (← goals.mapM fun goal => goal.withContext do
    let mut goal := goal
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if (← instantiateMVars decl.type).isAppOf ``Veir.IsFromVerifiedOp then
        goal ← goal.tryClear decl.fvarId
    return goal)

/-- Unfold the semantics of a gMIR pattern goal: the operation interpreters, the result-type
matches of `Attribute.of`, and the high bits chosen by each created `g_anyext`, which become a
universally quantified bit-vector. -/
macro "simpLegalSemantics" : tactic => `(tactic|
  simp [ctree_semantics, Sim.bind_monadLift_right_iff, Attribute.of, _root_.CTree.CTree.bind_tau,
    Sim.tau_l, -Attribute.integerType_eq_of])

/-- Normalize a gMIR validity goal after `simpLegalSemantics`: split the matched values and integer
types, substitute the widths the matcher fixes, then repeatedly resolve the width guards of extensions, split the remaining width and result-type
checks of the interpreters, and substitute the widths they equate. A `g_anyext` whose width guard
only resolves here exposes its chosen high bits at that point. -/
macro "normalizeLegalValid" : tactic => `(tactic| (
  intros
  clearVerified
  casesConformingValues
  all_goals casesIntegerTypes
  /- Reduce the widths of the split integer types, so that matched widths can be substituted. -/
  all_goals (try dsimp only at *)
  all_goals (try subst_vars)
  iterate 8 (
    /- Introduce the high bits chosen by the extensions resolved so far, and those chosen by the
    extensions among the matched operations. -/
    all_goals intros
    all_goals clearVerified
    all_goals (try casesExistsAnd)
    all_goals (try simp_all [RuntimeValue.isRefinedBy, le_eq_false_of_lt, lt_eq_false_of_le, Attribute.of,
      IntegerType.signless, Data.LLVM.trunc_ext, Data.LLVM.trunc_sext, ofInt_ofInt_value,
      PureOrErr.CanInterpretTo.tau_iff, PureOrErr.CanInterpretTo.tauG_iff,
      _root_.CTree.CTree.bind_tau, _root_.CTree.CTree.tau_def, Sim.tau_l, Sim.bind_monadLift_right_iff,
      -Attribute.integerType_eq_of])
    all_goals (try (exfalso; omega))
    all_goals (try splitGuards)
    all_goals (try casesResultTypes)
    all_goals (try subst_vars))
  all_goals (try simp_all [RuntimeValue.isRefinedBy, le_eq_false_of_lt, lt_eq_false_of_le, Attribute.of,
    _root_.CTree.CTree.bind_tau, _root_.CTree.CTree.tau_def, Sim.tau_l, Sim.bind_monadLift_right_iff,
    -Attribute.integerType_eq_of])
  all_goals (try (exfalso; omega))))

/-- Prove the validity of a gMIR pattern, closing each remaining value goal with the local
correctness lemma `lemma`. The pattern is first evaluated with `cbv`: its builders iterate over
the operand lists of the opcode, which `simp` cannot traverse once zipped with their handles. -/
macro "proveLegalValid" "using" lemma:term : tactic => `(tactic| (
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeLegalValid
  all_goals intros
  /- Strip the truncations of extended values that a narrow operation reads back. -/
  all_goals (try simp only [Data.LLVM.trunc_ext, Data.LLVM.trunc_sext])
  all_goals first
    | (apply $lemma <;> simp_all)
    | simp_all [$lemma:term]))

/-- Prove the validity of a gMIR pattern, closing each remaining value goal with the tactics
`closer`, for rules whose local correctness is an equation to rewrite with. -/
macro "proveLegalValid" "with" closer:tacticSeq : tactic => `(tactic| (
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeLegalValid
  all_goals intros
  all_goals (try simp only [Data.LLVM.trunc_ext, Data.LLVM.trunc_sext])
  all_goals ($closer)))

/-- Print the normalized goals of a gMIR pattern validity proof. Used to state local lemmas. -/
macro "probeLegalValid" : tactic => `(tactic| (
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeLegalValid
  trace_state
  all_goals sorry))

end Veir.Legalization.CTreeProofs
