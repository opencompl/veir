module

namespace Veir.Data.LLVM

public section

/--
The memory ordering of an atomic operation. Not every operation accepts every
ordering: a fence, for instance, needs at least `acquire`.
-/
inductive AtomicOrdering where
  | not_atomic
  | unordered
  | monotonic
  | acquire
  | release
  | acq_rel
  | seq_cst
deriving DecidableEq, Inhabited, Repr, Hashable

def AtomicOrdering.fromNat (s : Nat) : Option AtomicOrdering :=
  match s with
  | 0 => some .not_atomic
  | 1 => some .unordered
  | 2 => some .monotonic
  | 4 => some .acquire
  | 5 => some .release
  | 6 => some .acq_rel
  | 7 => some .seq_cst
  | _ => none

def AtomicOrdering.toNat : AtomicOrdering → Nat
  | .not_atomic => 0
  | .unordered => 1
  | .monotonic => 2
  | .acquire => 4
  | .release => 5
  | .acq_rel => 6
  | .seq_cst => 7

end

end Veir.Data.LLVM
