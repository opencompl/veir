module

import QPFTypes

/-!
# Example: possibly-infinite lists

`CoList a` is built as `Cofix` of the shape functor `CoListF a CoList = Unit ⊕ (a × CoList)`,
whose `QPF` and `IsPolynomial` instances are derived by `@[qpf]`.
-/

namespace QPFTypes.Test.CoList

open QPF (Cofix)

/-! ## The type -/

@[qpf] def CoListF (α CoList : liveParam Type) :=
    Unit ⊕ (α × CoList)

/-- Possibly-infinite lists. -/
def CoList (a : Type) : Type :=
  Cofix (@TypeFun.ofCurried 2 CoListF) #t[a]

variable {a b : Type}

/-! ## Constructors and destructor -/

@[match_pattern] def CoListF.nil : CoListF α β := .inl ()
def CoList.nil : CoList a := Cofix.mk .nil

@[match_pattern] def CoListF.cons (x : α) (xs : β) : CoListF α β := .inr (x, xs)
def CoList.cons (x : a) (xs : CoList a) : CoList a :=
  Cofix.mk (.cons x xs)

def CoList.dest (xs : CoList α) : CoListF α (CoList α) :=
  Cofix.dest xs

@[simp, grind =] theorem CoList.dest_nil :
    CoList.dest (CoList.nil : CoList a) = CoListF.nil :=
  Cofix.dest_mk _

@[simp, grind =] theorem CoList.dest_cons (x : a) (xs : CoList a) :
    CoList.dest (CoList.cons x xs) = CoListF.cons x xs :=
  Cofix.dest_mk _

end QPFTypes.Test.CoList
