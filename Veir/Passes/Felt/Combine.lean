import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Felt.Matching
-- Pull in the soundness proof so default `lake build` checks it.
-- (Existing Combines/Proofs.lean and InstructionSelection/Proofs.lean
-- are orphan files in the current lakefile; we depart from that
-- precedent here to defend against silent proof bitrot.)
import Veir.Passes.Felt.Proofs
-- Fully sorry-free, axiom-clean versions of ALL 15 Felt peephole rewrites (rewriter
-- preconditions discharged, not admitted). The `Combine` pass list below references them
-- unqualified; this file no longer defines any pattern itself.
import Veir.Passes.Felt.RewriteLemmas
-- F2 spike: the felt interpreter-semantics model + op-level bridge lemma.
-- Imported here so default `lake build` keeps the PoC alive (anti-bitrot).
import Veir.Passes.Felt.InterpModel

namespace Veir.FeltPass

/-!
  Felt-dialect peephole combines.

  15 peephole rewrites as of Tier 1+2 (2026-05-20). They cover **5 of
  the 18 `felt` opcodes** (`const`, `add`, `sub`, `mul`, `neg`); the
  other 13 (`div`, `inv`, `pow`, `uintdiv`/`sintdiv`, `umod`/`smod`,
  `bit_and`/`bit_or`/`bit_xor`/`bit_not`, `shl`/`shr`) are declared in
  the opcode enum but have no properties, matcher, pattern, proof, or
  interpreter case — the field- and prime-dependent ops are not ported.

  - Phase E.1–E.4 (4): `right_identity_zero_add` (x+0→x),
    `constant_fold_add` (c1+c2), `self_subtraction_to_zero` (x-x→0),
    `assoc_const_fold_add` ((x+c1)+c2→x+(c1+c2)).
  - Tier 1 (8): `right_identity_one_mul` (x·1→x), `right_zero_mul`
    (x·0→0), `constant_fold_sub` / `constant_fold_mul` /
    `constant_fold_neg`, `add_neg_to_zero` (x+(-x)→0),
    `neg_neg_to_self` (-(-x)→x), `add_const_swap` (canonicalize
    constants to right of `felt.add`).
  - Tier 2 (3): `add_sub_const_cancel` ((x+c)-c→x),
    `sub_add_const_cancel` ((x-c)+c→x), `assoc_const_fold_mul`
    ((x·c1)·c2 → x·(c1·c2)).

  ## What "verified" means here (read before relying on it)

  Two independent layers, both machine-checked and axiom-clean
  ([propext, Classical.choice, Quot.sound] — no `sorryAx`, no `WfIRContext.Dom`):

  1. ARITHMETIC. Each pattern has a paired theorem in `Veir/Passes/Felt/Proofs.lean`
     proving the **algebraic identity** over `Felt p := ZMod p` (holds in any commutative
     ring — primality is not threaded).
  2. IR WELL-FORMEDNESS. As of F1 (2026-06-01) **all 15** rewrites live in
     `RewriteLemmas.lean` with every `replaceValue`/`eraseOp`/`createOp`/`replaceOp`
     precondition DISCHARGED (not `sorry`-admitted), via the shared `projectToOperand` /
     `replaceWithNewOp` / `replaceWithBinOpOfConst` tails plus per-matcher in-bounds lemmas.
     Two facts `WfIRContext` does not carry (an op's region count, and result≠operand /
     op-has-parent) are supplied by sound defensive runtime guards (they only skip the
     rewrite in degenerate states impossible for well-formed matched IR).

  What is STILL NOT proven (the remaining trust boundary): that either layer is linked to
  the IR *interpreter* semantics — felt is not interpreted and `!felt.type` pins no prime
  (see REVIEW.md VC1/F2, and the F2 spike). So "verified" = arithmetic identity + IR
  well-formedness preservation, NOT semantic preservation.

  Style note: each pattern follows the same shape — syntactic `matchX`, build replacement
  op(s), `replaceValue` + `eraseOp` (pure projection) or `replaceOp` (synthesis).
-/

/-! # Lowering Patterns -/

-- All 15 Felt peephole rewrites are now the fully sorry-free, axiom-clean versions in
-- `RewriteLemmas.lean` (imported above), built on the shared `projectToOperand` (projection),
-- `replaceWithNewOp` (single-op synthesis) and `replaceWithBinOpOfConst` (two-op synthesis)
-- tails plus per-matcher in-bounds lemmas. They are referenced unqualified by the `Combine`
-- pass list below; this file no longer defines any pattern itself.

/-! # Pass implementation -/

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern
    #[ -- Phase E.1-E.4 originals
       right_identity_zero_add, constant_fold_add, self_subtraction_to_zero,
       assoc_const_fold_add,
       -- Tier 1: multiplicative identities, annihilation, constant folds, neg
       right_identity_one_mul, right_zero_mul, constant_fold_sub,
       constant_fold_mul, constant_fold_neg, add_neg_to_zero, neg_neg_to_self,
       add_const_swap,
       -- Tier 2: telescoping and mul-of-const associativity
       add_sub_const_cancel, sub_add_const_cancel, assoc_const_fold_mul ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying felt-combine pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "felt-combine"
    description := "Felt-dialect peephole combines (Tier 1+2: identities, constant folds, telescoping)"
    run := Combine.impl }

end Veir.FeltPass
