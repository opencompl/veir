module

import QPFTypes.Meta.QPFExpr.AddDecl

/-!
# `QPFExpr.addDecls` Unit Tests

Test that `QPFExpr.addDecls` adds the four declarations it promises, plus the
two `IsPolynomial` instances it adds when the `QPFExpr` is known to be
polynomial, for `QPFExpr`s that are built by hand out of the helpers in
`QPFTypes.Meta.QPFExpr.Basic`.

The sections below work outwards from the smallest interface: first `addDecls`
with neither universe level parameters nor dead variables, then each of those
two arguments in turn, then the properties every generated declaration has, and
finally `addDeclsInferringLevelParams`, which wraps `addDecls` by inferring the
level parameters instead of taking them.
-/

namespace QPFTypes.Test
open Lean QPFExpr

set_option QPFTypes.debug true

/-!
## The four declarations

The smallest call there is: no level parameters, no dead variables.
-/

run_meta addDecls (mkProj 0 (1 : Fin 2)) `QPFTypes.Test.Proj₁ []

/-- info: QPFTypes.Test.Proj₁.Uncurried : TypeFun 2 -/
#guard_msgs in #check Proj₁.Uncurried

/-- info: QPFTypes.Test.Proj₁ : CurriedTypeFun 2 -/
#guard_msgs in #check Proj₁

/-- The uncurried declaration is defined by exactly the `QPFExpr` it was given. -/
example : Proj₁.Uncurried = QPF.Prj (1 : Fin 2) := rfl

/-- The curried declaration is its `TypeFun.curry`, hence applies as expected. -/
example : Proj₁ = TypeFun.curry Proj₁.Uncurried := rfl
example (α β : Type) : Proj₁ α β = α := rfl

-- Both instances are registered

/-- info: Proj₁.Uncurried.instQPF -/
#guard_msgs in #synth QPF Proj₁.Uncurried

/-- info: Proj₁.instQPF -/
#guard_msgs in #synth QPF (TypeFun.ofCurried Proj₁)

-- A projection is polynomial, so both `IsPolynomial` instances are registered too

/-- info: Proj₁.Uncurried.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial Proj₁.Uncurried

/-- info: Proj₁.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial (TypeFun.ofCurried Proj₁)

/--
Each `IsPolynomial` instance is indexed by the `QPF` instance that `addDecls`
declared for the same type function, not by some other expression that happens
to be definitionally equal to it.
-/
example : @QPF.IsPolynomial 2 Proj₁.Uncurried Proj₁.Uncurried.instQPF := inferInstance
example : @QPF.IsPolynomial 2 (TypeFun.ofCurried Proj₁) Proj₁.instQPF := inferInstance

/-!
## Universe level parameters

The level parameters are taken as-is, exactly like `Lean.addDecl` takes them, so
a `QPFExpr` over `Level.param u` yields a universe-polymorphic declaration whose
parameter is named `u`.
-/

run_meta addDecls (mkProj (.param `u) (1 : Fin 2)) `QPFTypes.Test.PolyProj [`u]

/-- info: QPFTypes.Test.PolyProj.{u} : CurriedTypeFun 2 -/
#guard_msgs in #check PolyProj

example (α β : Type u) : PolyProj α β = α := rfl
universe u in
/-- info: PolyProj.instQPF -/
#guard_msgs in #synth QPF (TypeFun.ofCurried PolyProj.{u})

universe u in
/-- info: PolyProj.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial (TypeFun.ofCurried PolyProj.{u})

/-!
## Dead variables

The `deadVars` are free variables of the local context that the `QPFExpr` may
mention; all four declarations abstract over them, in the order given.
-/

run_meta Meta.withLocalDeclD `k (mkConst ``Nat) fun k =>
  addDecls (mkConstant 0 1 (mkApp (mkConst ``Fin) k)) `QPFTypes.Test.DeadFin [] #[k]

/-- info: QPFTypes.Test.DeadFin (k : Nat) : CurriedTypeFun 1 -/
#guard_msgs in #check DeadFin

/-- info: QPFTypes.Test.DeadFin.Uncurried (k : Nat) : TypeFun 1 -/
#guard_msgs in #check DeadFin.Uncurried

example (k : Nat) (α : Type) : DeadFin k α = Fin k := rfl
variable (k : Nat) in
/-- info: DeadFin.instQPF k -/
#guard_msgs in #synth QPF (TypeFun.ofCurried (DeadFin k))

-- The `IsPolynomial` instances abstract over the dead variables just the same.

variable (k : Nat) in
/-- info: DeadFin.Uncurried.instIsPolynomial k -/
#guard_msgs in #synth QPF.IsPolynomial (DeadFin.Uncurried k)

variable (k : Nat) in
/-- info: DeadFin.instIsPolynomial k -/
#guard_msgs in #synth QPF.IsPolynomial (TypeFun.ofCurried (DeadFin k))

/-!
## The instances carry executable code

The two type functions are `Type`-valued, so the compiler erases them, but the
two `QPF` instances are not: they carry `MvFunctor.map`, `QPF.abs` and
`QPF.repr`. Were the instance left uncompiled, this definition would be rejected
for depending on something noncomputable.
-/

def mapProj₁ {α β : TypeVec.{0} 2} (f : α ⟹ β) (x : Proj₁.Uncurried α) : Proj₁.Uncurried β :=
  MvFunctor.map f x

/-!
## Compositions

`Comp₀ α = α`, since `QPF.Comp` reads the last curried argument of the outer
binary functor from index `1` of the tuple.
-/

run_meta do
  let F := mkProj 0 (1 : Fin 2)
  let Gs := #v[mkConstant 0 1 (mkConst ``Nat), mkProj 0 (0 : Fin 1)]
  addDecls (← mkComp F Gs) `QPFTypes.Test.Comp₀ []

/-- info: QPFTypes.Test.Comp₀ : CurriedTypeFun 1 -/
#guard_msgs in #check Comp₀

example (α : Type) : Comp₀ α = α := rfl
/-- info: Comp₀.Uncurried.instQPF -/
#guard_msgs in #synth QPF Comp₀.Uncurried

/-- info: Comp₀.instQPF -/
#guard_msgs in #synth QPF (TypeFun.ofCurried Comp₀)

-- A composite of polynomial arguments is polynomial.

/-- info: Comp₀.Uncurried.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial Comp₀.Uncurried

/-- info: Comp₀.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial (TypeFun.ofCurried Comp₀)

/--
A composed instance is compiled just like the atomic one above. Note that this
check does not rely on `compileDecl` logging its errors: it fails at *this*
definition even when the instance was allowed to end up without code silently.
-/
def mapComp₀ {α β : TypeVec.{0} 1} (f : α ⟹ β) (x : Comp₀.Uncurried α) : Comp₀.Uncurried β :=
  MvFunctor.map f x

/-!
## Fixpoints

`mkFix` and `mkCofix` turn an `(n+1)`-ary QPF into an `n`-ary one, by taking the
least/greatest fixpoint of its last argument. `FixNat` is the fixpoint of the
binary constant functor on `Nat`, which ignores the recursive argument.
-/

run_meta addDecls (mkFix (mkConstant 0 2 (mkConst ``Nat))) `QPFTypes.Test.FixNat []

/-- info: QPFTypes.Test.FixNat : CurriedTypeFun 1 -/
#guard_msgs in #check FixNat

example : FixNat.Uncurried = QPF.Fix (QPF.Const 2 Nat) := rfl

/-- info: FixNat.Uncurried.instQPF -/
#guard_msgs in #synth QPF FixNat.Uncurried

/-- info: FixNat.instQPF -/
#guard_msgs in #synth QPF (TypeFun.ofCurried FixNat)

-- Taking the least fixpoint preserves polynomiality.

/-- info: FixNat.Uncurried.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial FixNat.Uncurried

/-- info: FixNat.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial (TypeFun.ofCurried FixNat)

-- The greatest fixpoint behaves the same way.

run_meta addDecls (mkCofix (mkConstant 0 2 (mkConst ``Nat))) `QPFTypes.Test.CofixNat []

/-- info: QPFTypes.Test.CofixNat : CurriedTypeFun 1 -/
#guard_msgs in #check CofixNat

example : CofixNat.Uncurried = QPF.Cofix (QPF.Const 2 Nat) := rfl

/-- info: CofixNat.Uncurried.instQPF -/
#guard_msgs in #synth QPF CofixNat.Uncurried

/-- info: CofixNat.instQPF -/
#guard_msgs in #synth QPF (TypeFun.ofCurried CofixNat)

/-- info: CofixNat.Uncurried.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial CofixNat.Uncurried

/-- info: CofixNat.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial (TypeFun.ofCurried CofixNat)

-- A fixpoint of a composite is polynomial as well, so polynomiality survives
-- being passed through more than one construction. `FixComp` is the fixpoint of
-- `fun (α, ρ) => ρ`, i.e. of the composition that drops the non-recursive
-- argument, taken at arity `1`.
run_meta do
  let F := mkProj 0 (1 : Fin 2)
  let Gs := #v[mkProj 0 (0 : Fin 2), mkProj 0 (1 : Fin 2)]
  addDecls (mkFix (← mkComp F Gs)) `QPFTypes.Test.FixComp []

/-- info: QPFTypes.Test.FixComp.Uncurried : TypeFun 1 -/
#guard_msgs in #check FixComp.Uncurried

/-- info: FixComp.Uncurried.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial FixComp.Uncurried

/-- info: FixComp.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial (TypeFun.ofCurried FixComp)
/-!
## Inferred level parameters

`addDeclsInferringLevelParams` is `addDecls` with the level parameters inferred
rather than given: every universe metavariable that is still unassigned becomes
a parameter of the declaration.
-/

run_elab do
  let u ← Meta.mkFreshLevelMVar
  addDeclsInferringLevelParams (mkProj u (1 : Fin 2)) `QPFTypes.Test.InferredProj

/-- info: QPFTypes.Test.InferredProj.{u_1} : CurriedTypeFun 2 -/
#guard_msgs in #check InferredProj

example (α β : Type u) : InferredProj α β = α := rfl
universe u in
/-- info: InferredProj.instQPF -/
#guard_msgs in #synth QPF (TypeFun.ofCurried InferredProj.{u})

universe u in
/-- info: InferredProj.instIsPolynomial -/
#guard_msgs in #synth QPF.IsPolynomial (TypeFun.ofCurried InferredProj.{u})

end QPFTypes.Test
