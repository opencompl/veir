import Veir.IR.WellFormed
import Veir.Rewriter.WfRewriter
import Veir.Dominance
import Veir.Passes.Matching
import Veir.Verifier
import Veir.Passes.InstructionSelection.Common
import Veir.Interpreter
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas

/-!
# Common tactics for instruction-selection rewrite proofs

These macros help drive `PreservesSemantics`-style proofs about local rewrites. A rewrite's pattern
is typically a chain of `bind`s that split on guard conditions and create ops one at a time, so the
tactics here "peel" that chain apart: they discharge the split conditions and introduce, for each
created op, the updated context, the new op, and its creation hypothesis (rewritten into a plain
`createOp` form). Several also transport a dominance hypothesis through each creation step so it stays
usable in the resulting context.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {rawCtx rawCtx' : IRContext OpInfo} {ctx ctx' : WfIRContext OpInfo}


open Lean in
/-- Split the `if`/`match` guarding `hpattern`, discharge the false branch with `grind`, and name the
    resulting facts `hyps`, simplifying `hpattern` in the surviving branch. -/
macro "peelSplittableCondition" "[" hyps:binderIdent* "]" hpattern:ident : tactic =>
  `(tactic| (
      split at $hpattern:ident; grind; rename_i $[$hyps]*
      try simp at $hpattern:ident
     ))

open Lean in
/-- Like `peelSplittableCondition`, but `grind` discharges the *other* branch (via `rotate_left`),
    keeping the first branch of the split. -/
macro "peelSplittableCondition'" "[" hyps:binderIdent* "]" hpattern:ident : tactic =>
  `(tactic| (
      split at $hpattern:ident; rotate_left; grind; rename_i $[$hyps]*
      try simp at $hpattern:ident
     ))

open Lean in
/-- Simplify `hpattern` to a three-way conjunction of equalities and substitute each one into the
    goal, clearing `hpattern`. -/
macro "cleanupHpattern" hpattern:ident : tactic =>
  `(tactic| (
      simp at $hpattern:ident; have ⟨ha, hb, hc⟩ := $hpattern:ident; clear $hpattern:ident
      subst ha hb hc
     ))

open Lean in
/-- Peel one op-creation step from `hpattern`, introducing the updated context `newCtx`, the created
    op `newOp`, and the creation hypothesis `hNewCtx`, leaving the rest of the pattern in `hpattern`. -/
macro "peelOpCreation" hpattern:ident newCtx:ident newOp:ident hNewCtx:ident : tactic =>
  `(tactic| (
      try simp only [Option.bind_eq_some_iff] at $hpattern:ident
      have ⟨⟨$newCtx, $newOp⟩, $hNewCtx, pat'⟩ := $hpattern:ident
      clear $hpattern:ident; have $hpattern:ident := pat'; clear pat'
     ))

open Lean in
/-- Peel a `castToRegLocal` creation from `hpattern` (like `peelOpCreation`), unfold it to the plain
    `createOp` form in `hCast`, and transport the dominance hypothesis `oldDom` into `newDom` over the
    new context `newCtx`. -/
macro "peelCastToRegLocal" hpattern:ident newCtx:ident newOp:ident hCast:ident
    oldDom:ident newDom:ident : tactic =>
  `(tactic| (
      peelOpCreation $hpattern:ident $newCtx:ident $newOp:ident $hCast:ident
      simp only [castToRegLocal] at $hCast:ident
      rw [WfRewriter.createOp!_none_eq (by grind) (by simp) (by simp)] at $hCast:ident
      have $newDom:ident := (ValuePtr.dominatesIp_before_WfRewriter_createOp $hCast:ident
        (by clear $hpattern:ident; grind) (by clear $hpattern:ident; grind)).mpr $oldDom:ident
     ))

open Lean in
/-- Like `peelOpCreation`, but also rewrites the peeled `createOp!` to the plain `createOp` form and
    transports the dominance hypothesis `oldDom` into `newDom` over `newCtx`. Dischargers clear the
    unpeeled `hpattern` so it stays available for later peels. -/
macro "peelOpCreation!" hpattern:ident newCtx:ident newOp:ident hNewCtx:ident
    oldDom:ident newDom:ident : tactic =>
  `(tactic| (
      peelOpCreation $hpattern:ident $newCtx:ident $newOp:ident $hNewCtx:ident
      rw [WfRewriter.createOp!_none_eq (by clear $hpattern:ident; grind)
        (by clear $hpattern:ident; simp) (by clear $hpattern:ident; simp)] at $hNewCtx:ident
      have $newDom:ident := (ValuePtr.dominatesIp_before_WfRewriter_createOp $hNewCtx:ident
        (by clear $hpattern:ident; grind) (by clear $hpattern:ident; grind)).mpr $oldDom:ident
     ))

open Lean in
/-- Like `peelCastToRegLocal`, but peels a `replaceWithRegLocal` creation into `hCastBack`,
    rewriting it to the plain `createOp` form and transporting the dominance hypothesis `oldDom`
    into `newDom` over `newCtx`. -/
macro "peelReplaceWithRegLocal" hpattern:ident newCtx:ident newOp:ident hCastBack:ident
    oldDom:ident newDom:ident : tactic =>
  `(tactic| (
      peelOpCreation $hpattern:ident $newCtx:ident $newOp:ident $hCastBack:ident
      simp only [replaceWithRegLocal] at $hCastBack:ident
      rw [WfRewriter.createOp!_none_eq (by clear $hpattern:ident; grind)
        (by clear $hpattern:ident; simp) (by clear $hpattern:ident; simp)] at $hCastBack:ident
      have $newDom:ident := (ValuePtr.dominatesIp_before_WfRewriter_createOp $hCastBack:ident
        (by clear $hpattern:ident; grind) (by clear $hpattern:ident; grind)).mpr $oldDom:ident
     ))

open Lean in
/-- Like `peelCastToRegLocal`, but transports *two* dominance hypotheses (one per matched
    operand of a binary lowering) through the creation step. -/
macro "peelCastToRegLocal₂" hpattern:ident newCtx:ident newOp:ident hCast:ident
    oldDom₁:ident newDom₁:ident oldDom₂:ident newDom₂:ident : tactic =>
  `(tactic| (
      peelCastToRegLocal $hpattern:ident $newCtx:ident $newOp:ident $hCast:ident
        $oldDom₁:ident $newDom₁:ident
      have $newDom₂:ident := (ValuePtr.dominatesIp_before_WfRewriter_createOp $hCast:ident
        (by clear $hpattern:ident; grind) (by clear $hpattern:ident; grind)).mpr $oldDom₂:ident
     ))

open Lean in
/-- Like `peelOpCreation!`, but transports *two* dominance hypotheses (one per matched operand of
    a binary lowering) through the creation step. -/
macro "peelOpCreation!₂" hpattern:ident newCtx:ident newOp:ident hNewCtx:ident
    oldDom₁:ident newDom₁:ident oldDom₂:ident newDom₂:ident : tactic =>
  `(tactic| (
      peelOpCreation! $hpattern:ident $newCtx:ident $newOp:ident $hNewCtx:ident
        $oldDom₁:ident $newDom₁:ident
      have $newDom₂:ident := (ValuePtr.dominatesIp_before_WfRewriter_createOp $hNewCtx:ident
        (by clear $hpattern:ident; grind) (by clear $hpattern:ident; grind)).mpr $oldDom₂:ident
     ))

open Lean in
/-- Like `peelReplaceWithRegLocal`, but transports *two* dominance hypotheses (one per matched
    operand of a binary lowering) through the creation step. -/
macro "peelReplaceWithRegLocal₂" hpattern:ident newCtx:ident newOp:ident hCastBack:ident
    oldDom₁:ident newDom₁:ident oldDom₂:ident newDom₂:ident : tactic =>
  `(tactic| (
      peelReplaceWithRegLocal $hpattern:ident $newCtx:ident $newOp:ident $hCastBack:ident
        $oldDom₁:ident $newDom₁:ident
      have $newDom₂:ident := (ValuePtr.dominatesIp_before_WfRewriter_createOp $hCastBack:ident
        (by clear $hpattern:ident; grind) (by clear $hpattern:ident; grind)).mpr $oldDom₂:ident
     ))
