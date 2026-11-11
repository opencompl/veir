module

public import Veir.IR.Simp
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
  /-- The matcher gives each operand and result of a type group its own type handle, so it
  accepts matches whose operands and results have different widths, which verified IR rules
  out. The gMIR interpreter computes the result at the operands' width, but the rewrite produces
  one of the matched result type, so the rewrite is only correct on well-typed matches. -/
  | needsTypedMatch
  /-- The rule is only correct at some target widths, e.g. `g_bswap`, which is only defined at
  widths 16, 32 and 64. -/
  | widthDependent
  /-- The local correctness lemma at every width is not proven yet. -/
  | notYetProven
  deriving Repr, DecidableEq

end

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
  casesConformingValues
  all_goals casesIntegerTypes
  /- Reduce the widths of the split integer types, so that matched widths can be substituted. -/
  all_goals (try dsimp only at *)
  all_goals (try subst_vars)
  iterate 8 (
    /- Introduce the high bits chosen by the extensions resolved so far. -/
    all_goals intros
    all_goals (try simp_all [RuntimeValue.isRefinedBy, le_eq_false_of_lt, lt_eq_false_of_le, Attribute.of,
      IntegerType.signless, Data.LLVM.trunc_ext, Data.LLVM.trunc_sext,
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
