import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1381
private theorem ashr_self (x : LLVM.Int w) (ex : Bool) :
    RuntimeValue.int w (LLVM.Int.ashr x x ex) ⊒ .int w (.val 0) := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run]
  | val a =>
    have hw : w < 2 ^ w := Nat.lt_two_pow_self
    have hn : (BitVec.ofNat w w).toNat = w := by simp [Nat.mod_eq_of_lt hw]
    by_cases ha : a.msb = true
    · have hb := BitVec.toNat_ge_of_msb_true ha
      have hc : w ≤ 2^(w-1) := by
        have hd := Nat.lt_two_pow_self (n := w-1)
        have hw0 : w ≠ 0 := by intro h; subst w; change false = true at ha; cases ha
        omega
      have hg : (BitVec.ofNat w w) ≤ a := by
        rw [BitVec.le_def, hn]
        omega
      simp [LLVM.Int.ashr, Id.run, pure, hg, RuntimeValue.isRefinedBy, isRefinedBy]
    · have ha' : a.msb = false := by simp_all
      simp [LLVM.Int.ashr, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy,
        BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_of_msb_false ha', BitVec.ushiftRight_self]
      grind
/-- X-X → 0, all scalar widths and all overflow flags. -/
def pattern_lshr : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .lshr) #[x,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_lshr_valid : Pattern.Valid pattern_lshr := by
  simp only [pattern_lshr]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x p v hi
  obtain rfl := (lshr_iff w p x x v).mp hi
  exists (.int w (.val (BitVec.ofNat w 0)))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run, pure]
    grind [BitVec.ushiftRight_self]
/-- X-X → 0, all scalar widths and all overflow flags. -/
def pattern_ashr : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .ashr) #[x,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_ashr_valid : Pattern.Valid pattern_ashr := by
  simp only [pattern_ashr]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x p v hi
  obtain rfl := (ashr_iff w p x x v).mp hi
  exists (.int w (.val (BitVec.ofNat w 0)))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · exact ashr_self _ _
end Veir.InstSimplify.IS1381
