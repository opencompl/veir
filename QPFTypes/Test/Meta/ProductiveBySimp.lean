module

import QPFTypes

/-!
# The `qpf_productive_by` simp set

`@[qpf_ctor]` states the layers in `g.__dest_partial` and `g.__get_dest_partial` in
`simp only [qpf_productive_by]` normal form, composing the generated proofs with the proof
produced by `simp`. Hence lemmas in the set need not be definitional: here, `Nat.zero_add` is not
(it is proved by induction).
-/

namespace QPFTypes.Test.ProductiveBySimp

open QPF

@[qpf] def StreamF (α S : liveParam Type) := α × S

def StreamF.cons (hd : α) (tl : S) : StreamF α S :=
  (hd, tl)

@[qpf] def Stream (a : Type) : Type :=
  Cofix (@TypeFun.ofCurried 2 StreamF) #t[a]

attribute [local qpf_productive_by] Nat.zero_add

/-- A constructor whose layer is only simplified by a non-definitional lemma. -/
@[qpf_ctor]
def Stream.consZeroAdd (x : Nat) (xs : Stream Nat) : Stream Nat :=
  Cofix.mk (.cons (0 + x) xs)

/--
info: QPFTypes.Test.ProductiveBySimp.Stream.consZeroAdd.__get_dest_partial (x : Nat) (xs : Stream.__partial Nat) :
  Comp.get (Cofix.dest (Stream.consZeroAdd.__partial x xs)) = some (StreamF.cons x xs)
-/
#guard_msgs in
#check Stream.consZeroAdd.__get_dest_partial

/--
info: QPFTypes.Test.ProductiveBySimp.Stream.consZeroAdd.__dest_partial (x : Nat) (xs : Stream.__partial Nat) :
  Cofix.dest (Stream.consZeroAdd.__partial x xs) = Comp.mk (some (StreamF.cons x xs))
-/
#guard_msgs in
#check Stream.consZeroAdd.__dest_partial

/--
info: QPFTypes.Test.ProductiveBySimp.Stream.consZeroAdd.__partial_injEq (x : Nat) (xs : Stream.__partial Nat) (x' : Nat)
  (xs' : Stream.__partial Nat) :
  (Stream.consZeroAdd.__partial x xs = Stream.consZeroAdd.__partial x' xs') = (x = x' ∧ xs = xs')
-/
#guard_msgs in
#check Stream.consZeroAdd.__partial_injEq

-- The injectivity lemma is in `qpf_productive_by`.
example (x y : Nat) (xs ys : Stream.__partial Nat) :
    Stream.consZeroAdd.__partial x xs = Stream.consZeroAdd.__partial y ys ↔ x = y ∧ xs = ys := by
  simp only [qpf_productive_by]

/-- A constructor whose layer is not injective in `x`: it gets no injectivity lemma. -/
@[qpf_ctor]
def Stream.consZero (x : Nat) (xs : Stream Nat) : Stream Nat :=
  Cofix.mk (.cons (0 * x) xs)

/-- error: Unknown constant `_private.Test.Meta.ProductiveBySimp.0.QPFTypes.Test.ProductiveBySimp.Stream.consZero.__partial_injEq` -/
#guard_msgs in
#check @Stream.consZero.__partial_injEq

end QPFTypes.Test.ProductiveBySimp
