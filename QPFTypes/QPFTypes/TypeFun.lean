module

public import QPFTypes.TypeVec

/-!
# TypeFun

`TypeFun.{u, v} n` is the type of uncurried `n`-ary type functions:
`TypeVec.{u} n → Type v`.  Argument types live in `Type u`; the result lives in `Type v`.

`CurriedTypeFun.{u} n` is the curried form `Type u → ··· → Type u` (`n` arguments,
result in `Type u`). The result universe must equal the argument universe; for a
heterogeneous result use `TypeFun.{u, v}` directly.

`TypeFun.curry` and `TypeFun.ofCurried` convert between `TypeFun.{u, u} n` and
`CurriedTypeFun.{u} n` and are mutually inverse.
-/
@[expose] public section

namespace QPFTypes

universe u v

set_option linter.checkUnivs false in
/-- An uncurried `n`-ary type function: arguments in `Type u`, result in `Type v`. -/
abbrev TypeFun (n : Nat) : Type (max (u + 1) (v + 1)) :=
  TypeVec.{u} n → Type v

section CurriedTypeFun

/-- A curried `n`-ary type function: `Type u → ··· → Type u` (`n` arguments). -/
abbrev CurriedTypeFun : Nat → Type (u + 1)
  | 0     => Type u
  | n + 1 => Type u → CurriedTypeFun n

end CurriedTypeFun

namespace TypeFun

/-! ## curry / ofCurried -/

/-- Convert an uncurried `TypeFun.{u, u} n` to a `CurriedTypeFun.{u} n`.

The first curried argument corresponds to `α.head` (the last `Fin` position), so for `n = 2`:
`curry F = fun α₀ α₁ => F (α₁ <: α₀ <: nil)`. -/
def curry : {n : Nat} → TypeFun.{u, u} n → CurriedTypeFun.{u} n
  | 0,   F => F TypeVec.nil
  | _+1, F => fun a => curry (fun αs => F (a <: αs))

/-- Convert a `CurriedTypeFun.{u} n` to an uncurried `TypeFun.{u, u} n`. -/
def ofCurried : {n : Nat} → CurriedTypeFun.{u} n → TypeFun.{u, u} n
  | 0,   F, _ => F
  | _+1, F, α => ofCurried (F α.head) α.tail

/-! ## Inverse laws -/

@[simp, grind =] theorem curry_ofCurried {n : Nat} (F : CurriedTypeFun.{u} n) :
    curry (ofCurried F) = F := by
  induction n <;> simp [curry, ofCurried, *]

@[simp]
theorem ofCurried_curry {n : Nat} (F : TypeFun.{u, u} n) :
    ofCurried (curry F) = F := by
  induction n
  · funext α
    simp [ofCurried, curry, α.eq_nil]
  · grind [ofCurried, curry]

end TypeFun

/-! ## AsTypeFun typeclass -/

set_option linter.checkUnivs false in
/-- `AsTypeFun n α` witnesses an equivalence between `α` and `TypeFun.{u, v} n`. -/
class AsTypeFun (n : outParam Nat) (α : Type _) where
  /-- Interpret `α` as a `TypeFun n`. -/
  toTypeFun   : α → TypeFun.{u, v} n
  /-- Reconstruct an `α` from a `TypeFun n`. -/
  ofTypeFun   : TypeFun.{u, v} n → α
  toTypeFun_ofTypeFun : ∀ F, toTypeFun (ofTypeFun F) = F := by grind
  ofTypeFun_toTypeFun : ∀ f, ofTypeFun (toTypeFun f) = f := by grind

attribute [simp, grind =] AsTypeFun.toTypeFun_ofTypeFun AsTypeFun.ofTypeFun_toTypeFun

/-- `CoeFun` instance: values of type `α` can be applied to a `TypeVec n`
    whenever `AsTypeFun n α` holds. -/
instance [AsTypeFun.{u, v} n α] : CoeFun α (fun _ => TypeVec.{u} n → Type v) where
  coe := AsTypeFun.toTypeFun

/-! ### Instances -/

/-- A `TypeFun` is trivially isomorphic to `TypeFun` -/
instance : AsTypeFun.{u, v} n (TypeFun.{u, v} n) where
  toTypeFun F := F
  ofTypeFun F := F

/-- A curried type function can be uncurried into a `TypeFun`. -/
instance : AsTypeFun.{u, u} n (CurriedTypeFun.{u} n) where
  toTypeFun F := TypeFun.ofCurried F
  ofTypeFun F := TypeFun.curry F
  toTypeFun_ofTypeFun F := TypeFun.ofCurried_curry F
  ofTypeFun_toTypeFun F := TypeFun.curry_ofCurried F

/-!
Although, say, `CurriedTypeFun 1` is def-eq to `Type → Type`,
the way this works is somewhat hackish, and does not interact particularly well
with typeclass synthesis.
Thus, we explicitly construct the isomorphism through the following instances.
-/

instance [AsTypeFun.{u, v} n α] : AsTypeFun (n + 1) (Type u → α) where
  toTypeFun F αs := AsTypeFun.toTypeFun (F αs.head) αs.tail
  ofTypeFun F a  := AsTypeFun.ofTypeFun (fun αs => F (a <: αs))
  toTypeFun_ofTypeFun F := by simp
  ofTypeFun_toTypeFun F := by simp

instance : AsTypeFun.{u, v} 0 (Type v) where
  toTypeFun α βs := α
  ofTypeFun F := F .nil
  toTypeFun_ofTypeFun F := by ext; simp [TypeVec.eq_nil]
  ofTypeFun_toTypeFun F := by simp

/-! ## Examples -/

example (α β : Type) :
    (TypeFun.ofCurried (n := 2) Sum) (α <: β <: TypeVec.nil) = Sum α β :=
  rfl

end QPFTypes
