import Veir.InstSimplify.FunnelExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Source rotate guard with power-of-two width mask, including comparison commutation. -/
def IS4923 (k : Nat) (left swapcmp swapand : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 2^k)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let c ← MatchProg.value ty
    let lim ← matchBitConstant ty (Int.ofNat (2^k-1))
    let rem ← MatchProg.operation (.llvm .and) (match swapand with | false => #[c,lim] | true => #[lim,c]) #[ty]
    let zero ← matchBitConstant ty 0
    let cmp ← MatchProg.operation (.llvm .icmp) (match swapcmp with | false => #[rem.res[0]!,zero] | true => #[zero,rem.res[0]!]) #[bt] (fun p => p.predicate == .eq)
    let f ← MatchProg.operation (.llvm (match left with | true => Llvm.intr__fshl | false => .intr__fshr)) #[x,x,c] #[ty]
    let _ ← MatchProg.root (.llvm .select) #[cmp.res[0]!,x,f.res[0]!] #[ty]
    return f.res[0]!) pure (fun x => x)
theorem IS4923_valid (k : Nat) (left swapcmp swapand : Bool) : Pattern.Valid (IS4923 k left swapcmp swapand) := by
  cases left <;> cases swapcmp <;> cases swapand
  all_goals
    simp only [IS4923, matchBitConstant]
    provePuddleValid
    rintro _ ⟨n,s⟩ rfl hn _ ⟨bw,bs⟩ rfl hb
    have hn : n = 2^k := by simpa using hn
    subst n
    have hb : bw = 1 := by simpa using hb
    subst bw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x c
    rintro lp lv li mp mv mi zp zv zi cp cv ch ci fp fv fi rp rv ri hl hz
    obtain rfl := matched_bit_constant_eq _ _ _ _ li hl
    obtain rfl := matched_bit_constant_eq _ _ _ _ zi hz
    have hp : cp.predicate = .eq := by simpa using ch
    obtain rfl := (and_iff _ _ _ _ _).mp mi
    obtain rfl := (icmp_iff _ _ _ _ _).mp ci
    first
    | obtain rfl := (fshl_iff _ _ _ _ _ _).mp fi
    | obtain rfl := (fshr_iff _ _ _ _ _ _).mp fi
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    cases c with
    | poison => simp [LLVM.Int.and,LLVM.Int.icmp,LLVM.Int.select,LLVM.Int.fshl,LLVM.Int.fshr,hp,RuntimeValue.isRefinedBy,isRefinedBy,Id.run]
    | val c =>
      have hr : (c &&& BitVec.ofNat (2^k) (2^k-1)).toNat = c.toNat % 2^k := by
        simp only [BitVec.toNat_and, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by have := (Nat.lt_two_pow_self (n := 2^k)); omega)]; exact Nat.and_two_pow_sub_one_eq_mod _ _
      try rw [LLVM.Int.and_comm]
      simp only [LLVM.Int.and,Id.run,pure,BitVec.ofInt_ofNat,BitVec.ofInt_natCast,Int.ofNat_eq_natCast,hp]
      try rw [BitVec.and_comm (BitVec.ofNat (2^k) (2^k-1)) c]
      first
      | have he := rotate_select_eq_zero false false x c _ hr; simp only at he; rw [he]
      | have he := rotate_select_eq_zero false true x c _ hr; simp only at he; rw [he]
      | have he := rotate_select_eq_zero true false x c _ hr; simp only at he; rw [he]
      | have he := rotate_select_eq_zero true true x c _ hr; simp only at he; rw [he]
      exact RuntimeValue.isRefinedBy_refl _
end Veir.InstSimplify
