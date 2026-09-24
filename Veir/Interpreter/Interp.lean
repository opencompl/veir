module

public import Veir.IR.Basic

public section

namespace Veir

/--
  The interpreter monad. An interpretation step has three outcomes. UB is a property
  of the execution, not of any value, so it lives here rather than inside
  `RuntimeValue` or `LLVM.Int`.
-/
inductive Interp (α : Type) where
  /-- Interpreter could not proceed (malformed IR, unsupported op) at `op`, if known. -/
  | fail (op : Option OperationPtr)
  /-- Execution triggered undefined behaviour at `op`, if known. -/
  | ub (op : Option OperationPtr)
  /-- Successful execution producing `a`. -/
  | ok (a : α)
deriving Inhabited

@[expose]
def Interp.map {α β : Type} (f : α → β) : Interp α → Interp β
  | .fail op => .fail op
  | .ub op => .ub op
  | .ok a => .ok (f a)

@[simp, grind =] theorem Interp.map_fail : Interp.map f (.fail op) = .fail op := rfl
@[simp, grind =] theorem Interp.map_ub : Interp.map f (.ub op) = .ub op := rfl
@[simp, grind =] theorem Interp.map_ok : Interp.map f (.ok a) = .ok (f a) := rfl

instance : Monad Interp where
  pure x := .ok x
  bind x f := match x with
    | .fail op => .fail op
    | .ub op => .ub op
    | .ok a => f a

instance : MonadLift Option Interp where
  monadLift
    | none => .fail none
    | some v => .ok v

@[simp, grind =] theorem Interp.pure_eq (a : α) : (pure a : Interp α) = .ok a := rfl
@[simp, grind =] theorem Interp.bind_ok (a : α) (f : α → Interp β) :
    (Interp.ok a >>= f) = f a := rfl
@[simp, grind =] theorem Interp.bind_ub (f : α → Interp β) :
    ((.ub op : Interp α) >>= f) = .ub op := rfl
@[simp, grind =] theorem Interp.bind_fail (f : α → Interp β) :
    ((.fail op : Interp α) >>= f) = .fail op := rfl
@[simp, grind =] theorem Interp.liftOption_none : ((none : Option α) : Interp α) = .fail none := rfl
@[simp, grind =] theorem Interp.liftOption_some (a : α) : ((some a : Option α) : Interp α) = .ok a := rfl

/-- Whether the interpretation failed, at any operation. -/
@[expose, simp, grind]
def Interp.isFail : Interp α → Bool
  | .fail _ => true
  | _ => false

/-- Whether the interpretation triggered UB, at any operation. -/
@[expose, simp, grind]
def Interp.isUB : Interp α → Bool
  | .ub _ => true
  | _ => false

/-- If reporting any failure or UB, blame `op` for it. -/
@[expose]
def Interp.withBlame (op : OperationPtr) : Interp α → Interp α
  | .fail none => .fail (some op)
  | .ub none => .ub (some op)
  | x => x

@[simp, grind =] theorem Interp.withBlame_ok : (Interp.ok a).withBlame op = .ok a := rfl

@[simp, grind =] theorem Interp.withBlame_eq_ok_iff (x : Interp α) :
    x.withBlame op = .ok a ↔ x = .ok a := by
  unfold Interp.withBlame; split <;> simp [reduceCtorEq]

@[simp, grind =] theorem Interp.isFail_withBlame (x : Interp α) :
    (x.withBlame op).isFail = x.isFail := by
  unfold Interp.withBlame; split <;> rfl

@[simp, grind =] theorem Interp.isUB_withBlame (x : Interp α) :
    (x.withBlame op).isUB = x.isUB := by
  unfold Interp.withBlame; split <;> rfl

end Veir
