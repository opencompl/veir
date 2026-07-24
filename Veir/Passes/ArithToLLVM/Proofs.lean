module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Refinement

import Veir.ForLean
import Veir.Meta.BVDecide
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Bitblast

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

public section

/-!
  Correctness proofs for the nontrivial lowering patterns in `ArithToLLVM.lean`.

  These proofs are specialized to i8 so that `veir_bv_decide` can discharge
  them. The left-hand side states the source operation's value semantics, and
  the right-hand side is the expression computed by the sequence of LLVM
  operations emitted by the corresponding rewrite. Division inputs for which
  the source operation has undefined behavior are explicit disjuncts.
-/

namespace Veir.Data.LLVM.Int

/--
`arith.ceildivui a, b` lowers to
`a == 0 ? 0 : ((a - 1) udiv b) + 1`.
-/
theorem ceildivui_lowering (a b : BitVec 8) :
    b = 0 ∨
      (val (if a = 0 then 0 else (a - 1).udiv b + 1) =
        let zero := constant 8 0
        let one := constant 8 1
        let isZero := icmp (val a) zero .eq
        let quotient := udiv (sub (val a) one) (val b)
        select isZero zero (add quotient one)) := by
  veir_bv_decide

/--
`arith.ceildivsi a, b` lowers to truncating signed division followed by a
one-unit correction when the quotient is inexact and the operands have the
same sign.
-/
theorem ceildivsi_lowering (a b : BitVec 8) :
    b = 0 ∨ (a = BitVec.intMin 8 ∧ b = -1) ∨
      (let z := a.sdiv b
       val (if a ≠ z * b ∧ (a.slt 0) = (b.slt 0) then z + 1 else z) =
        let zero := constant 8 0
        let one := constant 8 1
        let z := sdiv (val a) (val b)
        let notExact := icmp (val a) (mul z (val b)) .ne
        let aNeg := icmp (val a) zero .slt
        let bNeg := icmp (val b) zero .slt
        let signEqual := icmp aNeg bNeg .eq
        let cond := and notExact signEqual
        select cond (add z one) z) := by
  veir_bv_decide

/--
`arith.floordivsi a, b` lowers to truncating signed division followed by a
negative one-unit correction when the quotient is inexact and the operands
have opposite signs.
-/
theorem floordivsi_lowering (a b : BitVec 8) :
    b = 0 ∨ (a = BitVec.intMin 8 ∧ b = -1) ∨
      (let z := a.sdiv b
       val (if a ≠ z * b ∧ (a.slt 0) ≠ (b.slt 0) then z - 1 else z) =
        let zero := constant 8 0
        let negOne := constant 8 (-1)
        let z := sdiv (val a) (val b)
        let notExact := icmp (val a) (mul z (val b)) .ne
        let aNeg := icmp (val a) zero .slt
        let bNeg := icmp (val b) zero .slt
        let signOpposite := icmp aNeg bNeg .ne
        let cond := and notExact signOpposite
        select cond (add z negOne) z) := by
  veir_bv_decide

/--
The two results of `arith.addui_extended` are reproduced by an unflagged
`llvm.add` and `llvm.icmp ult`.
-/
theorem addui_extended_lowering (a b : Int 8) :
    (add a b, uaddOverflowFlag a b) =
      let sum := add a b
      (sum, icmp sum a .ult) := by
  cases a <;> cases b <;> simp [uaddOverflowFlag, Id.run] <;> veir_bv_decide

/--
The two results of `arith.mulsi_extended` are reproduced by a low-half
multiply and by sign-extending to twice the width, multiplying, shifting right
by the original width, and truncating.
-/
theorem mulsi_extended_lowering (a b : Int 8) :
    (mul a b, smulHigh a b) =
      let aExt := sext a 16 (by omega)
      let bExt := sext b 16 (by omega)
      let wide := mul aExt bExt
      let shiftAmount := constant 16 8
      let highWide := lshr wide shiftAmount
      (mul a b, trunc highWide 8 false false (by omega)) := by
  cases a <;> cases b <;> simp [smulHigh, Id.run] <;> veir_bv_decide

/--
The two results of `arith.mului_extended` are reproduced by a low-half
multiply and by zero-extending to twice the width, multiplying, shifting right
by the original width, and truncating.
-/
theorem mului_extended_lowering (a b : Int 8) :
    (mul a b, umulHigh a b) =
      let aExt := zext a 16 false (by omega)
      let bExt := zext b 16 false (by omega)
      let wide := mul aExt bExt
      let shiftAmount := constant 16 8
      let highWide := lshr wide shiftAmount
      (mul a b, trunc highWide 8 false false (by omega)) := by
  cases a <;> cases b <;> simp [umulHigh, Id.run] <;> veir_bv_decide

end Veir.Data.LLVM.Int
