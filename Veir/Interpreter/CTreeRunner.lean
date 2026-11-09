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
    (freezeHandler : ∀ c, FreezeC c := fun
      | .mk _ => 0
      | .pointer => Data.Pointer.null) : Interp R :=
  match t.unfold with
  | .ret r => .ok r
  | .tau (.inl .c1) k => run (k PUnit.unit) freezeHandler
  | .tau (.inr c) k => run (k (freezeHandler c)) freezeHandler
  | .vis (.inl _) _ => .fail none
  | .vis (.inr _) _ => .ub none

end Veir
