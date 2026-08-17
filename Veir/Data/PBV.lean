module

public import Veir.Data.PBV.BitVec
public import Veir.Data.PBV.Mask
public import Veir.Data.PBV.Elim
public import Veir.Data.PBV.Push
public import Veir.Data.PBV.Examples

/-!
# Bounded parametric bitvector solving

Parametric bitvector formulas — statements quantified over one or more widths `w : Nat` — are
undecidable in general. By placing a bound on the widths we wish to consider, such a formula can
be transformed into a bit-blastable form and discharged by `bv_decide`. Naively, bounding the
widths means enumerating every assignment of concrete widths, generating a number of queries
exponential in the number of width parameters; the technique described here instead solves the
formula with a *single* QF_BV query.

At a high level, every variable of parametric width `w` is turned into a variable of a concrete
width `o`, with `w ≤ o`, which is then masked with `m := 2^w - 1`. The mask is encoded as the
bitvector constraint `m &&& (m + 1) = 0`, which is independent of `w` and so can be bit-blasted;
it is the *only* fact about `w` the solver is given. The rest of the formula is then adapted so
that everything is expressed in terms of the concrete width `o` and the masks.

## The steps

Given a constrained parametric bitvector formula and a bound on the widths for which we wish to
prove it, the tactic performs the following steps:

1. Introduce bounds for all parametric bitwidth variables, based on the provided bound.
2. Derive the blast width `o` (distinct from the provided bound, since concatenations can increase
   the required blast width).
3. Define `BitVec` width variables to replace the `Nat` widths.
4. Replace parametric-width variables with masked variables of concrete width `o`.
5. Translate masks expressed in terms of `Nat`s into `BitVec` constraints, and translate conditions
   on the widths into conditions on the masks (for example, a width being smaller than another).
6. Rewrite the parametric expression into a concrete, single-width formula.
7. Remove the hypotheses about the `Nat` widths.
8. Bit-blast using `bv_decide`.

## Where each step lives

* `Veir.Data.PBV.BitVec` — `BitVec` lemmas used by the translation; nothing PBV-specific.
* `Veir.Data.PBV.Mask` — steps 3 and 5: `maskOfWidth`, `IsMask`, and the mask constraint.
* `Veir.Data.PBV.Elim` — steps 3 and 4: `width_elim` and `var_elim`.
* `Veir.Data.PBV.Push` — step 6: pushing `setWidth o` from the root of the goal down to its leaves.
* `Veir.Data.PBV.Examples` — a manual trace of the whole pipeline.

## Status

Steps 1, 2, 7 and 8 are not yet upstreamed, and the tactic automating the pipeline does not exist
yet; `Veir.Data.PBV.Examples` performs every step by hand. The set of push lemmas in
`Veir.Data.PBV.Push` covers only the operations needed by those examples.

The algorithm and its original implementation are due to `@bollu`.
-/
