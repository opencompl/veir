module

/-!
# Poison Semantics
This file defines a generic `PoisonOr α` type, which other data types
can use to implement (LLVM) poison semantics.
-/

/--
Elements of type `PoisonOr α` are either `poison`, or values of type `α`.

`PoisonOr α` is simply a wrapper around `Option α`, but we generally prefer
`PoisonOr` when specifying poison semantics in dialects, as it's more
self-documenting.
-/
structure PoisonOr (α : Type) where
  ofOption :: toOption : Option α
  deriving DecidableEq

namespace PoisonOr

/-! ### Constructors-/
@[match_pattern] def poison : PoisonOr α := ⟨none⟩
@[match_pattern] def value : α → PoisonOr α := (⟨some ·⟩)

/--
`casesOn'` is a custom eliminator. By tagging it with `cases_eliminator`, we can
write `cases a?` in tactic mode and have it do a case-analysis in terms of the
`poison` or `value` constructors defined above rather than breaking the value
down into the underlying option.
-/
@[elab_as_elim, cases_eliminator]
def casesOn'.{u} {α : Type} {motive : PoisonOr α → Sort u}
    (a? : PoisonOr α)
    (poison : motive poison)
    (value : (a : α) → motive (value a))
    : motive a? :=
  match a? with
  | .poison => poison
  | .value a => value a

@[simp] theorem value_inj {a b : α} :
    @Eq (no_index _) (value a) (value b) ↔ a = b := by
    -- ^^ `value a = value b ↔ _`
  constructor
  · rintro ⟨⟩; rfl
  · exact fun h => h ▸ rfl

theorem poison_ne_value (a : α) :
    @Ne (no_index _) poison (value a) := by -- `poison ≠ value a`
  rintro ⟨⟩
theorem value_ne_poison (a : α) :
    @Ne (no_index _) (value a) poison := by -- `value a ≠ poison`
  rintro ⟨⟩

@[simp]
theorem ite_value_value {c : Prop} [Decidable c] {a b : α} :
    (if c then value a else value b : no_index _) = value (if c then a else b) := by
  split <;> rfl

/-! ### Formatting & Priting instances -/
instance [ToString α] : ToString (PoisonOr α) where
  toString
  | .poison  => "poison"
  | .value a => "(value " ++ addParenHeuristic (toString a) ++ ")"

/-! ### Monad instance and lemmas -/
instance : Monad PoisonOr where
  pure := value
  bind := fun a f => match a with
    | poison  => poison
    | value a => f a

def bind₂ (a : PoisonOr α) (b : PoisonOr β) (f : α → β → PoisonOr γ) : PoisonOr γ :=
  (a >>= fun x => b >>= f x)

section Lemmas

@[simp] theorem pure_def : pure = @value α := rfl

@[simp] theorem poison_bind : poison >>= f = poison := rfl
@[simp] theorem value_bind : value a >>= f = f a := rfl
@[simp] theorem bind_poison : a? >>= (fun _ => @poison β) = poison := by
  cases a? <;> rfl

@[simp] theorem map_poison : f <$> poison = poison := rfl
@[simp] theorem map_value : f <$> value a = value (f a) := rfl

@[simp]
theorem bind_if_then_poison_eq_ite_bind (p : Prop) [Decidable p] (x : PoisonOr α) :
    (if p then poison else x : no_index _) >>= f = if p then poison else x >>= f := by
-- /---------------------------^^^^^^^^^^
-- NOTE: the if-then-else has an implicit type argument, which will be `PoisonOr α`,
-- that is normally indexed in the discr_tree. Since we want this rewrite to apply
-- when this type is, say, LLVM.IntW, we ensure it is not indexed, using `no_index`
  split <;> simp

@[simp]
theorem bind_if_else_poison_eq_ite_bind (p : Prop) [Decidable p] (x : PoisonOr α) :
    (if p then x else poison : no_index _) >>= f = if p then x >>= f else poison := by
  split <;> simp

@[simp] theorem bind₂_poison_left : bind₂ poison b? f = poison := rfl
@[simp] theorem bind₂_poison_right : bind₂ a? poison f = poison := by
  cases a? <;> simp [bind₂]
@[simp] theorem bind₂_value : bind₂ (value a) (value b) f = f a b := rfl
end Lemmas

instance : LawfulMonad PoisonOr where
  map_const := by intros; rfl
  id_map := by rintro _ (_|_) <;> rfl
  seqLeft_eq := by rintro _ _ (_|_) _ <;> rfl
  seqRight_eq := by rintro _ _ (_|_) (_|_) <;> rfl
  pure_seq := by intros; rfl
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl
  pure_bind _ _ := value_bind
  bind_assoc := by rintro _ _ _ (_|_) _ _ <;> rfl

/-! ## isPoison & getValue-/

/-- Returns whether the element is poison. -/
def isPoison : PoisonOr α → Bool
  | poison => true
  | value _ => false

/-- Returns the value of the element, or a default value if it is poison. -/
def getValue [Inhabited α] : PoisonOr α → α
  | poison => default
  | value a => a

section Lemmas
variable {a : α}

@[simp] theorem isPoison_poison : isPoison (@poison α) = true := rfl
@[simp] theorem isPoison_value : isPoison (value a) = false := rfl

@[simp] theorem getValue_value [Inhabited α] : (value a).getValue = a := rfl
@[simp] theorem getValue_poison [Inhabited α] : (@poison α).getValue = default := rfl

@[simp] theorem mk_some (x : α) : { toOption := some x } = PoisonOr.value x := rfl
@[simp] theorem mk_none : { toOption := none (α := α) } = PoisonOr.poison := rfl

@[simp]
theorem toOption_getSome : (PoisonOr.value x).toOption.getD y = x := rfl
@[simp]
theorem toOption_getNone : (PoisonOr.poison).toOption.getD y = y := rfl

end Lemmas

end PoisonOr
