module

public meta import Lean
public import QPFTypes.Theory.TypeVec.Basic
public import QPFTypes.Theory.TypeFun
public import QPFTypes.Meta.ProductiveBy.SimpSet

namespace QPFTypes

/-!
# Declarations in the `qpf_productive_by` simp set

Unfolding these reduces projections of literal vectors, such as
`(TypeVec.nil ::: α ::: β).tail.head`, to their entries (here, `β`): `head`, `tail`, `last` and
`drop` unfold to applications at indices `⟨i, h⟩`, at which the equations of `append1` apply.

The simproc `reduceOfCurried` turns applications such as
`TypeFun.ofCurried StreamF (TypeVec.nil ::: α ::: β)` into `StreamF α β`.
-/

open TypeVec in
attribute [qpf_productive_by] head last tail drop append1

attribute [qpf_productive_by] Option.some_inj exists_eq_left'

public meta section

open Lean Meta in
/--
Unfold `TypeFun.ofCurried F v`, for a literal vector `v` (built with `TypeVec.append1`), to
`F v.head v.tail.head ...`, whose arguments the rest of `qpf_productive_by` then reduces.

This cannot be done with lemmas (or by adding `ofCurried` to the simp set):
* since `ofCurried` is an `abbrev`, `simp` indexes `TypeFun.ofCurried F v` by its reducible
  unfolding `F v.head ...`, so no lemma about `ofCurried` (such as its equations) ever matches;
* unfolding `ofCurried` itself also unfolds the type function `TypeFun.ofCurried F` where it is
  not applied, as in `CofixWithBot (TypeFun.ofCurried F) α`, eta-expanding it to
  `fun α => F (α ⟨1, _⟩) (α ⟨0, _⟩)`.

For the same reason, this simproc is indexed by `_`, and checks the shape of the term itself.
-/
dsimproc [qpf_productive_by] reduceOfCurried (_) := fun e => do
  unless e.isAppOfArity ``QPFTypes.TypeFun.ofCurried 3 do return .continue
  unless e.appArg!.consumeMData.isAppOf ``QPFTypes.TypeVec.append1 do return .continue
  let e' ← withReducible <| whnf e
  if e' == e then return .continue
  return .visit e'

end
