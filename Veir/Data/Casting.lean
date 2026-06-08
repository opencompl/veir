module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.LLVM.Int.Bitblast
public import Veir.Data.RISCV.Reg.Basic
public import Veir.Data.RISCV.Reg.Simp
import all Veir.Data.LLVM.Int.Bitblast

public section

/-!
  This file defines the conversions between different types used in lowering passes.
  These represent the semantics of `builtin.unrealized_conversion_cast` operations.
-/


/--
  Cast `LLVM.Int` to `RISCV.Reg`.
-/
@[grind]
def LLVM.Int.toReg (i : Veir.Data.LLVM.Int w) : Veir.Data.RISCV.Reg :=
  match i with
  | .poison => .mk 0#64
  | .val bv => .mk (bv.zeroExtend 64)

/--
  Cast `RISCV.Reg` to `LLVM.Int`.
-/
@[grind]
def RISCV.Reg.toInt (r : Veir.Data.RISCV.Reg) (w : Nat) : Veir.Data.LLVM.Int w :=
  Veir.Data.LLVM.Int.val (BitVec.zeroExtend w r.val)

@[llvm_toBitVec, grind =]
theorem toInt_eq_val {r : Veir.Data.RISCV.Reg} :
    (RISCV.Reg.toInt r 64).getValue = r.val := by
  simp [RISCV.Reg.toInt, Veir.Data.LLVM.Int.getValue]

@[llvm_toBitVec, grind =]
theorem toInt_isPoison {r : Veir.Data.RISCV.Reg} :
    (RISCV.Reg.toInt r w).isPoison = false := by
  simp [RISCV.Reg.toInt, Veir.Data.LLVM.Int.isPoison]

@[llvm_toBitVec, grind =]
theorem val_toReg{i : Veir.Data.LLVM.Int w} :
    (LLVM.Int.toReg i).val = if h : i.isPoison = true then 0#64 else i.getValue.zeroExtend 64 := by
  simp only [LLVM.Int.toReg, BitVec.truncate_eq_setWidth]
  split
  · simp [Veir.Data.LLVM.Int.isPoison]
  · simp [llvm_toBitVec]
