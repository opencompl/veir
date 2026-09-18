module

namespace Veir

public section

/--
  The choices the interpreter makes where the semantics is nondeterministic.
  The interpreter is a function, so every such choice is drawn from the
  oracle, indexed by how many choices of that kind were made before, and two
  programs being compared are run against the same oracle.
-/
structure Oracle where
  /--
    The bits that the `n`-th `freeze` of a value with poison bits substitutes
    for them, at width `w`. Zero by default, which is what the interpreter
    always picked before.
  -/
  freeze : (n : Nat) → (w : Nat) → BitVec w := fun _ _ => 0

instance : Inhabited Oracle := ⟨{}⟩

end

end Veir
