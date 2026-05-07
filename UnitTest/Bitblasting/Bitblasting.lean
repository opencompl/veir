import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Simp
import Veir.Data.Refinement

open Veir.Data.LLVM.Int

/-!
  This file contains some of the `InstCombine` tests retrieved from Lean-MLIR,
  instantiated for integers with width `64`:
  https://github.com/opencompl/lean-mlir/blob/77fa1c1507a61369f6d9a8ab3de54b9bbe5e1393/SSA/Projects/InstCombine/AliveStatements.lean#L1

  We exclude the tests comprising unsupported operations, such as `neg` and `not`.
-/

/-- We introduce a tactic to automatically prove all the lemmas. -/
macro "llvm_bv_decide" : tactic =>
  `(tactic| ((try simp [llvm_toBitVec]; try bv_decide); all_goals sorry))

set_option warn.sorry false

/-
  `LLVM.not` is not supported in
  example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
      add (add (xor (and e_1 e) e) (constant 64 1)) e_2 ⊑ sub e_2 (or e_1 (not e)) := by sorry
-/

example
    (e e_1 : Veir.Data.LLVM.Int 1) : add e_1 e ⊑ xor e_1 e := by
  llvm_bv_decide

example
    (e : Veir.Data.LLVM.Int 64) : (add e e) ⊑
        (shl e (constant 64 1)) := by
  llvm_bv_decide

example
    (e e_1 : Veir.Data.LLVM.Int 64) : add (sub (constant 64 0) e) e_1 ⊑ sub e_1 e := by
  llvm_bv_decide

example
    (e e_1 : Veir.Data.LLVM.Int 64) :
      add (sub (constant 64 0) e) (sub (constant 64 0) e_1) ⊑ sub (constant 64 0) (add e e_1) := by
  llvm_bv_decide

example
    (e e_1 : Veir.Data.LLVM.Int 64) : add e (sub (constant 64 0) e_1) ⊑ sub e e_1 := by
  llvm_bv_decide

example
    (e e_1 : Veir.Data.LLVM.Int 64) : add (xor e (constant 64 (-1))) e_1 ⊑ sub (sub e_1 (constant 64 1)) e := by
  llvm_bv_decide

example
    (e e_1 : Veir.Data.LLVM.Int 64) : add (and e e_1) (xor e e_1) ⊑ or e e_1 := by
  llvm_bv_decide

example
    (e e_1 : Veir.Data.LLVM.Int 64) : add (and e e_1) (or e e_1) ⊑ add e e_1 := by
  llvm_bv_decide

example
    (e e_1 : Veir.Data.LLVM.Int 64) : sub e_1 (sub (constant 64 0) e) ⊑ add e_1 e := by
  llvm_bv_decide

/-
  `LLVM.neg` is not supported in

  example
      (e e_1 : Veir.Data.LLVM.Int 64) : sub e e_1 ⊑ add e (neg e_1) := by
-/

example (e e_1 : Veir.Data.LLVM.Int 1) :
    sub e_1 e ⊑ xor e_1 e := by
  llvm_bv_decide

example (e : Veir.Data.LLVM.Int 64) :
    sub (constant 64 (-1)) e ⊑ xor e (constant 64 (-1)) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    sub e_1 (xor e (constant 64 (-1))) ⊑ add e (add e_1 (constant 64 1)) := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    sub e_1 (add e e_2) ⊑ sub (sub e_1 e_2) e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    sub e_1 (add e_1 e) ⊑ sub (constant 64 0) e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    sub (sub e_1 e) e_1 ⊑ sub (constant 64 0) e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    sub (or e e_1) (xor e e_1) ⊑ and e e_1 := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    and (xor e e_1) e_2 ⊑ xor (and e e_2) (and e_1 e_2) := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    and (or e e_1) e_2 ⊑ and (or e (and e_1 e_2)) e_2 := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    and (icmp (and e e_1) (constant 64 0) Veir.Data.LLVM.IntPred.eq)
      (icmp (and e e_2) (constant 64 0) Veir.Data.LLVM.IntPred.eq) ⊑
      icmp (and e (or e_1 e_2)) (constant 64 0) Veir.Data.LLVM.IntPred.eq := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    and (icmp (and e e_1) e_1 Veir.Data.LLVM.IntPred.eq)
      (icmp (and e e_2) e_2 Veir.Data.LLVM.IntPred.eq) ⊑
      icmp (and e (or e_1 e_2)) (or e_1 e_2) Veir.Data.LLVM.IntPred.eq := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    and (icmp (and e e_1) e Veir.Data.LLVM.IntPred.eq)
      (icmp (and e e_2) e Veir.Data.LLVM.IntPred.eq) ⊑
      icmp (and e (and e_1 e_2)) e Veir.Data.LLVM.IntPred.eq := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (icmp e e_1 Veir.Data.LLVM.IntPred.sgt) (icmp e e_1 Veir.Data.LLVM.IntPred.ne) ⊑
      icmp e e_1 Veir.Data.LLVM.IntPred.sgt := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (icmp e (constant 64 0) Veir.Data.LLVM.IntPred.eq)
      (icmp e_1 (constant 64 0) Veir.Data.LLVM.IntPred.eq) ⊑
      icmp (or e e_1) (constant 64 0) Veir.Data.LLVM.IntPred.eq := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (icmp e e_1 Veir.Data.LLVM.IntPred.eq) (icmp e e_1 Veir.Data.LLVM.IntPred.ne) ⊑ constant 1 0 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (xor e (constant 64 (-1))) (xor e_1 (constant 64 (-1))) ⊑
      xor (or e e_1) (constant 64 (-1)) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (or e e_1) (xor (and e e_1) (constant 64 (-1))) ⊑ xor e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (xor (and e e_1) (constant 64 (-1))) (or e e_1) ⊑ xor e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (xor e e_1) e ⊑ and e (xor e_1 (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (or (xor e (constant 64 (-1))) e_1) e ⊑ and e e_1 := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    and (xor e e_2) (xor (xor e_2 e_1) e) ⊑ and (xor e e_2) (xor e_1 (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    and (or e e_1) (xor (xor e (constant 64 (-1))) e_1) ⊑ and e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (icmp e e_1 Veir.Data.LLVM.IntPred.ugt) (icmp e e_1 Veir.Data.LLVM.IntPred.eq) ⊑
      icmp e e_1 Veir.Data.LLVM.IntPred.uge := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (icmp e e_1 Veir.Data.LLVM.IntPred.uge) (icmp e e_1 Veir.Data.LLVM.IntPred.ne) ⊑ constant 1 1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (icmp e_1 (constant 64 0) Veir.Data.LLVM.IntPred.eq) (icmp e e_1 Veir.Data.LLVM.IntPred.ult) ⊑
      icmp (add e_1 (constant 64 (-1))) e Veir.Data.LLVM.IntPred.uge := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (icmp e_1 (constant 64 0) Veir.Data.LLVM.IntPred.eq) (icmp e_1 e Veir.Data.LLVM.IntPred.ugt) ⊑
      icmp (add e_1 (constant 64 (-1))) e Veir.Data.LLVM.IntPred.uge := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (icmp e (constant 64 0) Veir.Data.LLVM.IntPred.ne) (icmp e_1 (constant 64 0) Veir.Data.LLVM.IntPred.ne) ⊑
      icmp (or e e_1) (constant 64 0) Veir.Data.LLVM.IntPred.ne := by
  llvm_bv_decide

/-
  `LLVM.not` is not supported in
  example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    or (xor e e_1) e_2 ⊑ xor (or e e_2) (and e_1 (not e_2)) := by sorry
-/

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (and (xor e (constant 64 (-1))) e_1) e ⊑ or e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (and e e_1) (xor e (constant 64 (-1))) ⊑ or (xor e (constant 64 (-1))) e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (and e (xor e_1 (constant 64 (-1)))) (xor e e_1) ⊑ xor e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (and e (xor e_1 (constant 64 (-1)))) (and (xor e (constant 64 (-1))) e_1) ⊑ xor e e_1 := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    or (xor e e_2) (xor (xor e_2 e_1) e) ⊑ or (xor e e_2) e_1 := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    or (and (or e_2 e_1) e) e_2 ⊑ or e_2 (and e e_1) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (xor e (constant 64 (-1))) (xor e_1 (constant 64 (-1))) ⊑ xor (and e e_1) (constant 64 (-1)) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or e_1 (xor e_1 e) ⊑ or e_1 e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or e (xor (xor e (constant 64 (-1))) e_1) ⊑ or e (xor e_1 (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (and e e_1) (xor e e_1) ⊑ or e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or e (xor (or e e_1) (constant 64 (-1))) ⊑ or e (xor e_1 (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or e (xor (xor e e_1) (constant 64 (-1))) ⊑ or e (xor e_1 (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    or (and e e_1) (xor (xor e (constant 64 (-1))) e_1) ⊑ xor (xor e (constant 64 (-1))) e_1 := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    or (or e e_1) e_2 ⊑ or (or e e_2) e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (and (xor e (constant 64 (-1))) e_1) (constant 64 (-1)) ⊑ or e (xor e_1 (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (or (xor e (constant 64 (-1))) e_1) (constant 64 (-1)) ⊑ and e (xor e_1 (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (and e_1 e) (constant 64 (-1)) ⊑ or (xor e_1 (constant 64 (-1))) (xor e (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (or e_1 e) (constant 64 (-1)) ⊑ and (xor e_1 (constant 64 (-1))) (xor e (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (ashr (xor e_1 (constant 64 (-1))) e) (constant 64 (-1)) ⊑ ashr e_1 e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (icmp e_1 e Veir.Data.LLVM.IntPred.slt) (constant 1 (-1)) ⊑ icmp e_1 e Veir.Data.LLVM.IntPred.sge := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (sub e_1 e) (constant 64 (-1)) ⊑ add e (sub (constant 64 (-1)) e_1) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (add e e_1) (constant 64 (-1)) ⊑ sub (sub (constant 64 (-1)) e_1) e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (or e e_1) e_1 ⊑ and e (xor e_1 (constant 64 (-1))) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (and e e_1) e_1 ⊑ and (xor e (constant 64 (-1))) e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (and e e_1) (or e e_1) ⊑ xor e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (or e (xor e_1 (constant 64 (-1)))) (or (xor e (constant 64 (-1))) e_1) ⊑ xor e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (and e (xor e_1 (constant 64 (-1)))) (and (xor e (constant 64 (-1))) e_1) ⊑ xor e e_1 := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    xor (xor e e_1) (or e e_2) ⊑ xor (and (xor e (constant 64 (-1))) e_2) e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (and e e_1) (xor e e_1) ⊑ or e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (and e (xor e_1 (constant 64 (-1)))) (xor e (constant 64 (-1))) ⊑ xor (and e e_1) (constant 64 (-1)) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    xor (icmp e e_1 Veir.Data.LLVM.IntPred.ule) (icmp e e_1 Veir.Data.LLVM.IntPred.ne) ⊑
      icmp e e_1 Veir.Data.LLVM.IntPred.uge:= by
  llvm_bv_decide

example (e : Veir.Data.LLVM.Int 64) :
    mul e (constant 64 (-1)) ⊑ sub (constant 64 0) e := by
  llvm_bv_decide

/--
  expected error: The SAT solver timed out while solving the problem.
  example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
      mul (add e e_1) e_2 ⊑ add (mul e e_2) (mul e_1 e_2) := by llvm_bv_decide
-/

example (e e_1 : Veir.Data.LLVM.Int 64) :
    mul (sub (constant 64 0) e_1) (sub (constant 64 0) e) ⊑ mul e_1 e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 5) :
    mul (udiv e_1 e) e ⊑ sub e_1 (urem e_1 e) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 5) :
    mul (sdiv e_1 e) e ⊑ sub e_1 (srem e_1 e) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 5) :
    mul (sdiv e_1 e) (sub (constant 5 0) e) ⊑ sub (srem e_1 e) e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 5) :
    mul (udiv e_1 e) (sub (constant 5 0) e) ⊑ sub (urem e_1 e) e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 1) :
    mul e_1 e ⊑ and e_1 e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    mul (shl (constant 64 1) e) e_1 ⊑ shl e_1 e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 9) :
    sdiv (sub e (srem e e_1)) e_1 ⊑ sdiv e e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 9) :
    udiv (sub e (urem e e_1)) e_1 ⊑ udiv e e_1 := by
  llvm_bv_decide

example (e : Veir.Data.LLVM.Int 64) :
    sdiv e (constant 64 (-1)) ⊑ sub (constant 64 0) e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 1) :
    select e (xor e (constant 1 (-1))) e_1 ⊑ and (xor e (constant 1 (-1))) e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 1) :
    select e e_1 (xor e (constant 1 (-1))) ⊑ or (xor e (constant 1 (-1))) e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    select (constant 1 1) e_1 e ⊑ e_1 := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    select (constant 1 0) e_1 e ⊑ e := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    lshr (shl e e_1) e_1 ⊑ and e (lshr (constant 64 (-1)) e_1) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    shl (lshr e e_1) e_1 ⊑ and e (shl (constant 64 (-1)) e_1) := by
  llvm_bv_decide

example (e e_1 e_2 e_3: Veir.Data.LLVM.Int 64) :
    shl (xor e (and (lshr e_1 e_2) e_3)) e_2 ⊑ xor (and e_1 (shl e_3 e_2)) (shl e e_2) := by
  llvm_bv_decide

example (e e_1 e_2 e_3: Veir.Data.LLVM.Int 64) :
    shl (or (and (lshr e_1 e_2) e_3) e) e_2 ⊑ or (and e_1 (shl e_3 e_2)) (shl e e_2) := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    lshr (xor e e_2) e_1 ⊑ xor (lshr e e_1) (lshr e_2 e_1) := by
  llvm_bv_decide

example (e e_1 e_2 : Veir.Data.LLVM.Int 64) :
    shl (add e e_2) e_1 ⊑ add (shl e e_1) (shl e_2 e_1) := by
  llvm_bv_decide

example (e e_1 : Veir.Data.LLVM.Int 64) :
    lshr (shl e e_1) e_1 ⊑ and e (lshr (constant 64 (-1)) e_1) := by
  llvm_bv_decide
