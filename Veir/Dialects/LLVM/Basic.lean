module

namespace Veir.Dialects.LLVM

public inductive LLVMInt (w : Nat) where
  | value : BitVec w → LLVMInt w
  | poison : LLVMInt w

public def LLVMInt.decEq (x y : LLVMInt w) : Decidable (Eq x y) :=
  match x, y with
  | .value n, .value m => sorry
  | _, _ => sorry

public instance : DecidableEq (LLVMInt w) := LLVMInt.decEq

public def add {w : Nat} (a b : LLVMInt w) : LLVMInt w :=
  match a, b with
  | .value va, .value vb => .value (va + vb)
  | _, _ => .poison

public instance : Add (LLVMInt n) := ⟨add⟩

public def mul {w : Nat} (a b : LLVMInt w) : LLVMInt w :=
  match a, b with
  | .value va, .value vb => .value (va * vb)
  | _, _ => .poison

public instance : Mul (LLVMInt n) := ⟨mul⟩


end Veir.Dialects.LLVM
