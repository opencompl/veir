module

public import Veir.Data.PBV.Mask
public import Veir.Data.PBV.Elim
public import Veir.Data.PBV.Push
import Veir.Data.PBV.Examples

/-!
# Bounded parametric bitvector solving

Parametric bitvector formulas are in general undecidable, but by placing a bound
on the widths we wish to consider the formula can be transformed into a
bit-blastable form, discharged by `bv_decide`. Naively, bounding the widths means
enumerating and generating queries exponential in the number of width parameters.
The technique presented here solves a given formula in a single QF_BV query.

For example we might want to prove addition is commutative for all bitvectors
of width up to 64:
```
theorem add_comm_bv64 (w : Nat) (x y : BitVec w) (hw : w ≤ 64)
  : x + y = y + x := by
  ...
```

At a high-level, every variable of some parametric width `w` is transformed into
a variable of some concrete width `o`, with `w <= o`, and then it is masked with
`m := 2^w - 1`. The mask is encoded as a bv constraint `m &&& (m + 1) = 0`,
independent of the `w` parameter, allowing for bit-blasting. The rest of the
formula is then adapted so that everything is expressed in terms of the concrete
width `o` and the masks.

## The steps

Given a constrained parametric bitvector formula and a bound on the widths for
which we wish to prove it, the tactic performs the following steps:

1. Introduce bounds for all width variables, based on the provided bound.
2. Derive the blast width `o` (distinct from the provided bound, since
   operations (eg. concatenation) can increase the required blast width).
3. Define `BitVec` width variables to replace the `Nat` widths.
4. Replace parametric-width variables with masked variables of concrete width `o`.
5. Translate masks expressed in terms of `Nat`s into `BitVec` constraints,
   and translate conditions on the widths into conditions on the masks.
6. Rewrite the parametric expression into a concrete, single-width formula.
7. Remove the hypotheses about the `Nat` widths.
8. Bit-blast using `bv_decide`.

## Where each step lives

* `Veir.Data.PBV.Lemmas` — `Nat` and `BitVec` lemmas used by the translation.
* `Veir.Data.PBV.Elim` — steps 3 and 4: `width_elim` and `var_elim`.
* `Veir.Data.PBV.Mask` — step 5: `maskOfWidth`, the mask constraint.
* `Veir.Data.PBV.Push` — step 6: pushing `setWidth` from the root to its leaves.
* `Veir.Data.PBV.Examples` — a manual trace of the whole pipeline.

-/
