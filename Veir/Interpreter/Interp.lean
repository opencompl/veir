module

public section

namespace Veir

/--
  The interpreter monad. An interpretation step has three outcomes. UB is a property
  of the execution, not of any value, so it lives here rather than inside
  `RuntimeValue` or `LLVM.Int`.
-/
inductive Interp (α : Type) where
  /-- Interpreter could not proceed (malformed IR, unsupported op). -/
  | fail
  /-- Execution triggered undefined behaviour. -/
  | ub
  /-- Successful execution producing `a`. -/
  | ok (a : α)
deriving Inhabited

@[expose]
def Interp.map {α β : Type} (f : α → β) : Interp α → Interp β
  | .fail => .fail
  | .ub => .ub
  | .ok a => .ok (f a)

@[simp, grind =] theorem Interp.map_fail : Interp.map f .fail = .fail := rfl
@[simp, grind =] theorem Interp.map_ub : Interp.map f .ub = .ub := rfl
@[simp, grind =] theorem Interp.map_ok : Interp.map f (.ok a) = .ok (f a) := rfl

instance : Monad Interp where
  pure x := .ok x
  bind x f := match x with
    | .fail => .fail
    | .ub => .ub
    | .ok a => f a

instance : MonadLift Option Interp where
  monadLift
    | none => .fail
    | some v => .ok v

@[simp, grind =] theorem Interp.pure_eq (a : α) : (pure a : Interp α) = .ok a := rfl
@[simp, grind =] theorem Interp.bind_ok (a : α) (f : α → Interp β) :
    (Interp.ok a >>= f) = f a := rfl
@[simp, grind =] theorem Interp.bind_ub (f : α → Interp β) :
    ((.ub : Interp α) >>= f) = .ub := rfl
@[simp, grind =] theorem Interp.bind_fail (f : α → Interp β) :
    ((.fail : Interp α) >>= f) = .fail := rfl
@[simp, grind =] theorem Interp.liftOption_none : ((none : Option α) : Interp α) = .fail := rfl
@[simp, grind =] theorem Interp.liftOption_some (a : α) : ((some a : Option α) : Interp α) = .ok a := rfl

end Veir
