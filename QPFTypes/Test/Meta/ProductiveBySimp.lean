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

end QPFTypes.Test.ProductiveBySimp
