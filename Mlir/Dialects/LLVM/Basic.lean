module

namespace Mlir.Dialects.LLVM

public inductive LLVMInt (w : Nat) where
  | value : BitVec w → LLVMInt w
  | poison : LLVMInt w

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


end Mlir.Dialects.LLVM
