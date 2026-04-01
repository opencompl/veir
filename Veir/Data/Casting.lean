import Veir.Data.LLVM.Int.Basic
import Veir.Data.RISCV.Reg.Basic

/-!
  This file defines the conversions between different types used in lowering passes.
  These represent the semantics of `builtin.unrealized_conversion_cast` operations.
-/


/--
  Cast `LLVM.Int` to `RISCV.Reg`.
-/
def LLVM.Int.toReg (i : Veir.Data.LLVM.Int w) : Veir.Data.RISCV.Reg :=
  match i with
  | .poison => .mk 0#64
  | .val bv => .mk (bv.zeroExtend 64)

/--
  Cast `RISCV.Reg` to `LLVM.Int`.
-/
def RISCV.Reg.toInt (r : Veir.Data.RISCV.Reg) (w : Nat) : Veir.Data.LLVM.Int w :=
  Veir.Data.LLVM.Int.val (BitVec.zeroExtend w r.val)
