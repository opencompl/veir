module

namespace Veir.Data.LLVM

public section

/-- How the linker picks among the members of a comdat group. -/
inductive ComdatKind where
  | any
  | exactmatch
  | largest
  | nodeduplicate
  | samesize
deriving DecidableEq, Inhabited, Repr, Hashable

def ComdatKind.fromNat (s : Nat) : Option ComdatKind :=
  match s with
  | 0 => some .any
  | 1 => some .exactmatch
  | 2 => some .largest
  | 3 => some .nodeduplicate
  | 4 => some .samesize
  | _ => none

def ComdatKind.toNat : ComdatKind → Nat
  | .any => 0
  | .exactmatch => 1
  | .largest => 2
  | .nodeduplicate => 3
  | .samesize => 4

end

end Veir.Data.LLVM
