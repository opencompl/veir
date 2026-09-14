module

namespace Veir.Data.LLVM

public section

/--
The predicate of an `llvm.fcmp`.
-/
inductive FloatPred where
  | _false
  | oeq
  | ogt
  | oge
  | olt
  | ole
  | one
  | ord
  | ueq
  | ugt
  | uge
  | ult
  | ule
  | une
  | uno
  | _true
deriving DecidableEq, Inhabited, Repr, Hashable

def FloatPred.fromNat (s : Nat) : Option FloatPred :=
  match s with
  | 0 => some ._false
  | 1 => some .oeq
  | 2 => some .ogt
  | 3 => some .oge
  | 4 => some .olt
  | 5 => some .ole
  | 6 => some .one
  | 7 => some .ord
  | 8 => some .ueq
  | 9 => some .ugt
  | 10 => some .uge
  | 11 => some .ult
  | 12 => some .ule
  | 13 => some .une
  | 14 => some .uno
  | 15 => some ._true
  | _ => none

def FloatPred.toNat : FloatPred → Nat
  | ._false => 0
  | .oeq => 1
  | .ogt => 2
  | .oge => 3
  | .olt => 4
  | .ole => 5
  | .one => 6
  | .ord => 7
  | .ueq => 8
  | .ugt => 9
  | .uge => 10
  | .ult => 11
  | .ule => 12
  | .une => 13
  | .uno => 14
  | ._true => 15

end

end Veir.Data.LLVM
