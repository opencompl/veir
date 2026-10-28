module

public meta import Lean

/-!
# The `qpf_productive_by` simp set

Declarations unfolded to clean up the goals presented in a `productive_by` block: they reduce
projections of literal `TypeVec`s, such as `(TypeVec.nil ::: α ::: β).tail.head`, which appear
in the type arguments of layers like `StreamF.cons` (elaborated against
`TypeFun.ofCurried StreamF (TypeVec.nil ::: α ::: β)`). The declarations are tagged in
`QPFTypes.Meta.ProductiveBy.SimpLemmas`.

`productive_by_intro` ends with `simp only [qpf_productive_by]`, and `@[qpf_ctor]` states the
right-hand sides of `g.__dest_partial` and `g.__get_dest_partial` in `simp only
[qpf_productive_by]` normal form. The lemmas in this set need not hold by `rfl`.
-/

public meta section

/-- Simp set for cleaning up `productive_by` goals, see `QPFTypes.Meta.ProductiveBy.SimpSet`. -/
register_simp_attr qpf_productive_by
