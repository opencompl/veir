module

public import Veir.Prelude

public section

namespace Veir
namespace Analysis

/-
A result type used to indicate if a change happened. Boolean operations on
`ChangeResult` behave as though `Change` is truth.
-/
inductive ChangeResult where
  | noChange
  | change
deriving Inhabited, Repr, DecidableEq

namespace ChangeResult

def or (lhs rhs : ChangeResult) : ChangeResult :=
  match lhs with
  | .change => .change
  | .noChange => rhs

def and (lhs rhs : ChangeResult) : ChangeResult :=
  match lhs with
  | .noChange => .noChange
  | .change => rhs

instance : HOr ChangeResult ChangeResult ChangeResult where
  hOr := or

instance : HAnd ChangeResult ChangeResult ChangeResult where
  hAnd := and

end ChangeResult

/-- A semilattice that provides a join operation. -/
class JoinSemiLattice (α : Type u) where
  join : α → α → α := fun _ incoming => incoming

/-- A semilattice that provides a meet operation. -/
class MeetSemiLattice (α : Type u) where
  meet : α → α → α := fun current _ => current

/-- A type with a distinguished top element. -/
class Top (α : Type u) where
  top : α

/-- A type with a distinguished bottom element. -/
class Bot (α : Type u) where
  bottom : α

/-- A join-semilattice that also has top and bottom. -/
class BoundedJoinSemiLattice (α : Type u)
    extends JoinSemiLattice α, Top α, Bot α

/-- A meet-semilattice that also has top and bottom. -/
class BoundedMeetSemiLattice (α : Type u)
    extends MeetSemiLattice α, Top α, Bot α

/-- A bounded lattice with both join and meet operations. -/
class BoundedLattice (α : Type u)
    extends JoinSemiLattice α, MeetSemiLattice α, Top α, Bot α

instance [BoundedLattice α] : BoundedJoinSemiLattice α where
  join := JoinSemiLattice.join
  top := Top.top
  bottom := Bot.bottom

instance [BoundedLattice α] : BoundedMeetSemiLattice α where
  meet := MeetSemiLattice.meet
  top := Top.top
  bottom := Bot.bottom

infixl:65 " ⊔ " => JoinSemiLattice.join
infixl:70 " ⊓ " => MeetSemiLattice.meet
notation "⊤" => Top.top
notation "⊥" => Bot.bottom

/-
Join `incoming` into `current`, returning the updated state and whether it changed.
-/
def joinWithChange [JoinSemiLattice α] [DecidableEq α] (current incoming : α) : α × ChangeResult :=
  let updated := current ⊔ incoming
  if updated == current then
    (current, .noChange)
  else
    (updated, .change)

end Analysis
end Veir
