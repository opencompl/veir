import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Felt.Matching
-- Pull in the soundness proof so default `lake build` checks it.
-- (Existing Combines/Proofs.lean and InstructionSelection/Proofs.lean
-- are orphan files in the current lakefile; we depart from that
-- precedent here to defend against silent proof bitrot.)
import Veir.Passes.Felt.Proofs
-- Fully sorry-free, axiom-clean versions of `right_identity_zero_add` and
-- `constant_fold_add` (rewriter preconditions discharged, not admitted).
import Veir.Passes.Felt.RewriteLemmas

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

  Each pattern has a paired theorem in `Veir/Passes/Felt/Proofs.lean`
  proving the **algebraic identity** over `Felt p := ZMod p` (Phase
  E.5; holds in any commutative ring — primality is not threaded). That
  theorem is machine-checked and axiom-clean. **However**, the link
  from the theorem to the IR rewrite is NOT proven: every rewriter
  well-formedness precondition below is discharged with `sorry`
  (`set_option warn.sorry false` suppresses the warning), so this pass
  transitively depends on `sorryAx`. The theorems justify the *arithmetic*;
  they do not establish that the *IR transformation* is semantics- or
  well-formedness-preserving. Discharging the preconditions (via the
  sorry-free `WfRewriter` layer) is tracked as follow-up. See `REVIEW.md`
  (findings VC2/VC3) for the full trust-boundary writeup.

  Style note: each pattern follows the same shape — syntactic
  `matchX`, build replacement op(s), `replaceValue` + `eraseOp` (for
  pure projection) or `replaceOp` (when synthesizing a new op).
-/

/-! # Lowering Patterns -/

-- `right_identity_zero_add` (felt.add x (felt.const 0) → x) and
-- `constant_fold_add` (felt.add (const c1) (const c2) → const (c1+c2)) are now
-- the fully sorry-free, axiom-clean versions in `RewriteLemmas.lean` (imported
-- above). They are referenced unqualified by the `Combine` pass list below.
-- The remaining 13 patterns still admit their rewriter preconditions with
-- `sorry` (see REVIEW.md VC2); porting them onto the same lemma library +
-- defensive-guard recipe is tracked follow-up.

set_option warn.sorry false in
/-- felt.sub x x -> felt.const 0 -/
def self_subtraction_to_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSub op rewriter.ctx | return rewriter
  -- ValuePtr equality: both operands flow from the same SSA value.
  if lhs ≠ rhs then return rewriter
  -- Extract the operand's felt-type so the synthesized const's
  -- structured attribute (fieldType) matches its own result type.
  -- Without this, on bn254-typed felt the synthesized const would
  -- carry `#felt<const 0> : !felt.type` while having result type
  -- `!felt.type<"bn254">` — which LLZK rejects.
  let resultType := lhs.getType! rewriter.ctx.raw
  let Attribute.feltType ft := resultType.val | return rewriter
  let cstProp : FeltConstProperties :=
    { value := { value := 0, fieldType := ft } }
  let (rewriter, newOp) ← rewriter.createOp (OpCode.felt Felt.const)
    #[resultType] #[] #[] #[] cstProp (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/--
  felt.add (felt.add x c1) c2  ->  felt.add x (c1+c2)
  when c1 and c2 are felt.const literals.

  Doesn't require dominance reasoning beyond what `getDefiningOp!`
  provides: the inner add's operands and the outer constant are
  visible from the outer add's match, and we replace the outer add
  in-place (no SSA value is referenced before defined).
-/
def assoc_const_fold_add (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (innerVal, c2Val, _) := matchAdd op rewriter.ctx | return rewriter
  -- Outer add's rhs must be a constant.
  let some c2 := matchConstFromValue c2Val rewriter.ctx | return rewriter
  -- Outer add's lhs must be the result of another felt.add (x + c1).
  let some (x, c1Val, _) := matchAddFromValue innerVal rewriter.ctx | return rewriter
  -- Inner add's rhs must be a constant.
  let some c1 := matchConstFromValue c1Val rewriter.ctx | return rewriter
  -- VC3: require matching field types before folding (see constant_fold_add).
  if c1.value.fieldType ≠ c2.value.fieldType then return rewriter
  -- Build the combined constant (c1+c2) and create a fresh add.
  let combinedVal := c1.value.value + c2.value.value
  let combinedCst : FeltConstProperties :=
    { value := { value := combinedVal, fieldType := c1.value.fieldType } }
  let resultType := x.getType! rewriter.ctx.raw
  let (rewriter, combinedConstOp) ← rewriter.createOp (OpCode.felt Felt.const)
    #[resultType] #[] #[] #[] combinedCst (some <| .before op) sorry sorry sorry sorry
  -- The new add's RHS is the combined constant we just created.
  let combinedConstVal : ValuePtr := .opResult ⟨combinedConstOp, 0⟩
  let (rewriter, newAdd) ← rewriter.createOp (OpCode.felt Felt.add)
    #[resultType] #[x, combinedConstVal] #[] #[] ()
    (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newAdd sorry sorry sorry sorry sorry

/-! # Tier 1 patterns (E.5 follow-up, 2026-05-20)

  Patterns matching the Tier 1 identities proved in `Proofs.lean`.
  Each follows the same shape as the four pioneering patterns above:
  syntactic match, build replacement, replace+erase. Rewriter
  preconditions are discharged with `sorry` (consistent with VEIR
  pass-side practice).
-/

set_option warn.sorry false in
/-- felt.mul x (felt.const 1) -> x.  Soundness: `right_identity_one_mul`. -/
def right_identity_one_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchMul op rewriter.ctx | return rewriter
  let some rhsOp := rhs.getDefiningOp! rewriter.ctx.raw | return rewriter
  let some cst := matchConst rhsOp rewriter.ctx | return rewriter
  if cst.value.value ≠ 1 then return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- felt.mul x (felt.const 0) -> felt.const 0.  Soundness: `right_zero_mul`. -/
def right_zero_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchMul op rewriter.ctx | return rewriter
  let some rhsOp := rhs.getDefiningOp! rewriter.ctx.raw | return rewriter
  let some cst := matchConst rhsOp rewriter.ctx | return rewriter
  if cst.value.value ≠ 0 then return rewriter
  -- Synthesize a `felt.const 0` of the same type as the input (cf.
  -- `self_subtraction_to_zero` for the fieldType extraction trick).
  let resultType := lhs.getType! rewriter.ctx.raw
  let Attribute.feltType ft := resultType.val | return rewriter
  let zeroProp : FeltConstProperties :=
    { value := { value := 0, fieldType := ft } }
  let (rewriter, newOp) ← rewriter.createOp (OpCode.felt Felt.const)
    #[resultType] #[] #[] #[] zeroProp (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- felt.sub (felt.const c1) (felt.const c2) -> felt.const (c1-c2). -/
def constant_fold_sub (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSub op rewriter.ctx | return rewriter
  let some cstL := matchConstFromValue lhs rewriter.ctx | return rewriter
  let some cstR := matchConstFromValue rhs rewriter.ctx | return rewriter
  -- VC3: require matching field types before folding (see constant_fold_add).
  if cstL.value.fieldType ≠ cstR.value.fieldType then return rewriter
  let diffVal := cstL.value.value - cstR.value.value
  let cstProp : FeltConstProperties :=
    { value := { value := diffVal, fieldType := cstL.value.fieldType } }
  let resultType := lhs.getType! rewriter.ctx.raw
  let (rewriter, newOp) ← rewriter.createOp (OpCode.felt Felt.const)
    #[resultType] #[] #[] #[] cstProp (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- felt.mul (felt.const c1) (felt.const c2) -> felt.const (c1*c2). -/
def constant_fold_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchMul op rewriter.ctx | return rewriter
  let some cstL := matchConstFromValue lhs rewriter.ctx | return rewriter
  let some cstR := matchConstFromValue rhs rewriter.ctx | return rewriter
  -- VC3: require matching field types before folding (see constant_fold_add).
  if cstL.value.fieldType ≠ cstR.value.fieldType then return rewriter
  let prodVal := cstL.value.value * cstR.value.value
  let cstProp : FeltConstProperties :=
    { value := { value := prodVal, fieldType := cstL.value.fieldType } }
  let resultType := lhs.getType! rewriter.ctx.raw
  let (rewriter, newOp) ← rewriter.createOp (OpCode.felt Felt.const)
    #[resultType] #[] #[] #[] cstProp (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- felt.neg (felt.const c) -> felt.const (-c). -/
def constant_fold_neg (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchNeg op rewriter.ctx | return rewriter
  let some cst := matchConstFromValue operand rewriter.ctx | return rewriter
  let negVal := -cst.value.value
  let cstProp : FeltConstProperties :=
    { value := { value := negVal, fieldType := cst.value.fieldType } }
  let resultType := operand.getType! rewriter.ctx.raw
  let (rewriter, newOp) ← rewriter.createOp (OpCode.felt Felt.const)
    #[resultType] #[] #[] #[] cstProp (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- felt.add x (felt.neg x) -> felt.const 0.  Soundness: `add_neg_to_zero`. -/
def add_neg_to_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchAdd op rewriter.ctx | return rewriter
  let some (innerVal, _) := matchNegFromValue rhs rewriter.ctx | return rewriter
  -- Same SSA value going into both the lhs of the add and the operand
  -- of the neg.
  if lhs ≠ innerVal then return rewriter
  let resultType := lhs.getType! rewriter.ctx.raw
  let Attribute.feltType ft := resultType.val | return rewriter
  let zeroProp : FeltConstProperties :=
    { value := { value := 0, fieldType := ft } }
  let (rewriter, newOp) ← rewriter.createOp (OpCode.felt Felt.const)
    #[resultType] #[] #[] #[] zeroProp (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- felt.neg (felt.neg x) -> x.  Soundness: `neg_neg_to_self`. -/
def neg_neg_to_self (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchNeg op rewriter.ctx | return rewriter
  let some (inner, _) := matchNegFromValue operand rewriter.ctx | return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) inner sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/--
  felt.add (felt.const c) x  ->  felt.add x (felt.const c).
  Canonicalization: places constants on the right of `felt.add`, matching
  MLIR's convention. Combined with `right_identity_zero_add` etc., this
  lets the right-form rewrites fire even when the input had the constant
  on the left. Soundness: `add_const_swap`.

  Guarded against re-firing on the result: requires the *left* operand
  to be a constant *and* the right not to be — otherwise the rewriter's
  fixed-point loop would oscillate.
-/
def add_const_swap (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchAdd op rewriter.ctx | return rewriter
  let some _ := matchConstFromValue lhs rewriter.ctx | return rewriter
  -- Bail if the right is also a constant (let constant_fold_add handle it).
  if (matchConstFromValue rhs rewriter.ctx).isSome then return rewriter
  let resultType := lhs.getType! rewriter.ctx.raw
  let (rewriter, swapped) ← rewriter.createOp (OpCode.felt Felt.add)
    #[resultType] #[rhs, lhs] #[] #[] ()
    (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op swapped sorry sorry sorry sorry sorry

/-! # Tier 2 patterns (E.5 follow-up, 2026-05-20)

  Telescoping cancellations and multiplicative-constant associativity.
-/

set_option warn.sorry false in
/-- felt.sub (felt.add x c) c -> x.  Soundness: `add_sub_const_cancel`. -/
def add_sub_const_cancel (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (innerVal, outerC, _) := matchSub op rewriter.ctx | return rewriter
  let some outerCst := matchConstFromValue outerC rewriter.ctx | return rewriter
  let some (x, innerC, _) := matchAddFromValue innerVal rewriter.ctx | return rewriter
  let some innerCst := matchConstFromValue innerC rewriter.ctx | return rewriter
  if innerCst.value.value ≠ outerCst.value.value then return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) x sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- felt.add (felt.sub x c) c -> x.  Soundness: `sub_add_const_cancel`. -/
def sub_add_const_cancel (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (innerVal, outerC, _) := matchAdd op rewriter.ctx | return rewriter
  let some outerCst := matchConstFromValue outerC rewriter.ctx | return rewriter
  let some (x, innerC, _) := matchSubFromValue innerVal rewriter.ctx | return rewriter
  let some innerCst := matchConstFromValue innerC rewriter.ctx | return rewriter
  if innerCst.value.value ≠ outerCst.value.value then return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) x sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- felt.mul (felt.mul x c1) c2 -> felt.mul x (c1*c2). -/
def assoc_const_fold_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (innerVal, c2Val, _) := matchMul op rewriter.ctx | return rewriter
  let some c2 := matchConstFromValue c2Val rewriter.ctx | return rewriter
  let some (x, c1Val, _) := matchMulFromValue innerVal rewriter.ctx | return rewriter
  let some c1 := matchConstFromValue c1Val rewriter.ctx | return rewriter
  -- VC3: require matching field types before folding (see constant_fold_add).
  if c1.value.fieldType ≠ c2.value.fieldType then return rewriter
  let combinedVal := c1.value.value * c2.value.value
  let combinedCst : FeltConstProperties :=
    { value := { value := combinedVal, fieldType := c1.value.fieldType } }
  let resultType := x.getType! rewriter.ctx.raw
  let (rewriter, combinedConstOp) ← rewriter.createOp (OpCode.felt Felt.const)
    #[resultType] #[] #[] #[] combinedCst (some <| .before op) sorry sorry sorry sorry
  let combinedConstVal : ValuePtr := .opResult ⟨combinedConstOp, 0⟩
  let (rewriter, newMul) ← rewriter.createOp (OpCode.felt Felt.mul)
    #[resultType] #[x, combinedConstVal] #[] #[] ()
    (some <| .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newMul sorry sorry sorry sorry sorry

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
