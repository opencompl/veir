module

public import CTree.Defs
public import Veir.Interpreter.CTree

public section

open CTree

namespace Veir

/--
Run a tree with the `UBE`, `ErrorE`, and `FreezeC` effects. The handling for
`FreezeC` is provided by the `freezeHandler` argument.

TODO: Support LLUBI's '-undef-behavior=mode'. We currently choose 'zero' as the default instead of
'undef'.
-/
partial def Tree.run {R : Type} (t : Tree R)
    (freezeHandler : ∀ c, FreezeC c := fun _ => 0) : Interp R :=
  match t.unfold with
  | .ret r => .ok r
  | .tau (.inl .c1) k => run (k PUnit.unit) freezeHandler
  | .tau (.inr c) k => run (k (freezeHandler c)) freezeHandler
  | .vis (.inl _) _ => .fail none
  | .vis (.inr _) _ => .ub none

/-- Run a program tree. A call to a function without a body fails, as it cannot be interpreted. -/
def ProgramTree.run {R : Type} (t : ProgramTree R)
    (freezeHandler : ∀ c, FreezeC c := fun _ => 0) : Interp R :=
  Tree.run (CTree.interp (fun
    | .inl _ => fail
    | .inr e => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) e) t) freezeHandler

end Veir
