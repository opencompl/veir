module

public import Veir.Data.PBV.BitVec
public import Veir.Data.PBV.Mask
public import Veir.Data.PBV.Elim
public import Veir.Data.PBV.Push
public import Veir.Data.PBV.Examples

/-!
# Bounded parametric bitvector solving

Parametric bitvector formulas are in general undecidable, but by placing a bound on the widths we wish
to consider the formula can be transformed into a bit-blastable form, discharged by `bv_decide`.
Naively, bounding the widths means enumerating and generating queries exponential in the number of
widths parameters, in this technique the formula is solved by a single QF_BV query.

At a high-level, every variable of some parametric width `w` is transformed into a variable of some
concrete width `o`, with `w <= o`, and then it is masked with `m := 2^w - 1`. The mask is encoded as
a bitvector constraint `m &&& (m + 1) = 0`, independent of the `w` parameter, allowing for bit-blasting.
The rest of the formula is then adapted so that everything is expressed in terms of the concrete
width `o` and the masks.

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
* `Veir.Data.PBV.Mask` — step 5: `maskOfWidth`, `IsMask`, and the mask constraint.
* `Veir.Data.PBV.Elim` — steps 3 and 4: `width_elim` and `var_elim`.
* `Veir.Data.PBV.Push` — step 6: pushing `setWidth o` from the root of the goal down to its leaves.
* `Veir.Data.PBV.Examples` — a manual trace of the whole pipeline.

The algorithm and its original implementation were developed by `@bollu`.
-/
