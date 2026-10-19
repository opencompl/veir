import Veir.Dialects.Arith.Puddle

set_option linter.unusedSimpArgs false

namespace Veir.ArithCanonicalize.CommutativeSupport
open Veir Veir.Data

theorem add_comm_flags (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw = LLVM.Int.add y x nsw nuw := by
  cases x <;> cases y <;>
    simp [LLVM.Int.add, BitVec.add_comm, BitVec.saddOverflow_comm,
      BitVec.uaddOverflow_comm]

theorem mul_comm_flags (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.mul x y nsw nuw = LLVM.Int.mul y x nsw nuw := by
  exact LLVM.Int.mul_comm x y

theorem and_comm (x y : LLVM.Int w) : LLVM.Int.and x y = LLVM.Int.and y x := by
  cases x <;> cases y <;> simp [LLVM.Int.and, BitVec.and_comm]

theorem or_comm_flags (x y : LLVM.Int w) (disjoint : Bool) :
    LLVM.Int.or x y disjoint = LLVM.Int.or y x disjoint := by
  cases x <;> cases y <;> simp [LLVM.Int.or, BitVec.and_comm, BitVec.or_comm]

theorem xor_comm (x y : LLVM.Int w) : LLVM.Int.xor x y = LLVM.Int.xor y x := by
  cases x <;> cases y <;> simp [LLVM.Int.xor, BitVec.xor_comm]

theorem uaddOverflowFlag_comm (x y : LLVM.Int w) :
    LLVM.Int.uaddOverflowFlag x y = LLVM.Int.uaddOverflowFlag y x := by
  cases x <;> cases y <;>
    simp [LLVM.Int.uaddOverflowFlag, BitVec.uaddOverflow_comm]

theorem smulHigh_comm (x y : LLVM.Int w) :
    LLVM.Int.smulHigh x y = LLVM.Int.smulHigh y x := by
  cases x <;> cases y <;>
    simp [LLVM.Int.smulHigh, BitVec.mul_comm]

theorem umulHigh_comm (x y : LLVM.Int w) :
    LLVM.Int.umulHigh x y = LLVM.Int.umulHigh y x := by
  cases x <;> cases y <;>
    simp [LLVM.Int.umulHigh, BitVec.mul_comm]

theorem smax_comm (x y : LLVM.Int w) :
    LLVM.Int.smax x y = LLVM.Int.smax y x := by
  cases x <;> cases y <;> try simp [LLVM.Int.smax]
  rename_i a b
  by_cases heq : a = b
  · subst b
    simp [LLVM.Int.smax]
  · have hneq : a.toInt ≠ b.toInt := by
      intro hh
      exact heq ((BitVec.toInt_inj).mp hh)
    by_cases hle : a.toInt ≤ b.toInt
    · have hn : ¬ b.toInt ≤ a.toInt := by omega
      simp [LLVM.Int.smax, BitVec.sle, hle, hn]
    · have hrev : b.toInt ≤ a.toInt := by omega
      simp [LLVM.Int.smax, BitVec.sle, hle, hrev]

theorem smin_comm (x y : LLVM.Int w) :
    LLVM.Int.smin x y = LLVM.Int.smin y x := by
  cases x <;> cases y <;> try simp [LLVM.Int.smin]
  rename_i a b
  by_cases heq : a = b
  · subst b
    simp [LLVM.Int.smin]
  · have hneq : a.toInt ≠ b.toInt := by
      intro hh
      exact heq ((BitVec.toInt_inj).mp hh)
    by_cases hle : a.toInt ≤ b.toInt
    · have hn : ¬ b.toInt ≤ a.toInt := by omega
      simp [LLVM.Int.smin, BitVec.sle, hle, hn]
    · have hrev : b.toInt ≤ a.toInt := by omega
      simp [LLVM.Int.smin, BitVec.sle, hle, hrev]

theorem umax_comm (x y : LLVM.Int w) :
    LLVM.Int.umax x y = LLVM.Int.umax y x := by
  cases x <;> cases y <;> try simp [LLVM.Int.umax]
  rename_i a b
  by_cases heq : a = b
  · subst b
    simp [LLVM.Int.umax]
  · have hneq : a.toNat ≠ b.toNat := by
      intro hh
      exact heq ((BitVec.toNat_inj).mp hh)
    by_cases hle : a.toNat ≤ b.toNat
    · have hn : ¬ b.toNat ≤ a.toNat := by omega
      simp [LLVM.Int.umax, BitVec.ule, hle, hn]
    · have hrev : b.toNat ≤ a.toNat := by omega
      simp [LLVM.Int.umax, BitVec.ule, hle, hrev]

theorem umin_comm (x y : LLVM.Int w) :
    LLVM.Int.umin x y = LLVM.Int.umin y x := by
  cases x <;> cases y <;> try simp [LLVM.Int.umin]
  rename_i a b
  by_cases heq : a = b
  · subst b
    simp [LLVM.Int.umin]
  · have hneq : a.toNat ≠ b.toNat := by
      intro hh
      exact heq ((BitVec.toNat_inj).mp hh)
    by_cases hle : a.toNat ≤ b.toNat
    · have hn : ¬ b.toNat ≤ a.toNat := by omega
      simp [LLVM.Int.umin, BitVec.ule, hle, hn]
    · have hrev : b.toNat ≤ a.toNat := by omega
      simp [LLVM.Int.umin, BitVec.ule, hle, hrev]

end Veir.ArithCanonicalize.CommutativeSupport
