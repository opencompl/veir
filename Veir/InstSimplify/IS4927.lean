import Veir.InstSimplify.FunnelExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Source rotate guard with width remainder, including comparison commutation. -/
def IS4927 (w : Nat) (left swapcmp : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == w)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let c ← MatchProg.value ty
    let lim ← matchBitConstant ty w
    let rem ← MatchProg.operation (.llvm .urem) #[c,lim] #[ty]
    let zero ← matchBitConstant ty 0
    let cmp ← MatchProg.operation (.llvm .icmp) (match swapcmp with | false => #[rem.res[0]!,zero] | true => #[zero,rem.res[0]!]) #[bt] (fun p => p.predicate == .eq)
    let f ← MatchProg.operation (.llvm (match left with | true => Llvm.intr__fshl | false => .intr__fshr)) #[x,x,c] #[ty]
    let _ ← MatchProg.root (.llvm .select) #[cmp.res[0]!,x,f.res[0]!] #[ty]
    return f.res[0]!) pure (fun x => x)
theorem IS4927_valid (w : Nat) (left swapcmp : Bool) : Pattern.Valid (IS4927 w left swapcmp) := by
  cases left <;> cases swapcmp
  all_goals
    simp only [IS4927, matchBitConstant]
    provePuddleValid
    rintro _ ⟨n,s⟩ rfl hn _ ⟨bw,bs⟩ rfl hb
    have hn : n = w := by simpa using hn
    subst n
    have hb : bw = 1 := by simpa using hb
    subst bw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x c
    rintro lp lv li mp mv mi zp zv zi cp cv ch ci fp fv fi rp rv ri hl hz
    obtain rfl := matched_bit_constant_eq _ _ _ _ li hl
    obtain rfl := matched_bit_constant_eq _ _ _ _ zi hz
    have hp : cp.predicate = .eq := by simpa using ch
    obtain ⟨hub,rfl⟩ := (urem_iff _ _ _ _ _).mp mi
    obtain rfl := (icmp_iff _ _ _ _ _).mp ci
    first
    | obtain rfl := (fshl_iff _ _ _ _ _ _).mp fi
    | obtain rfl := (fshr_iff _ _ _ _ _ _).mp fi
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    cases c with
    | poison => simp [LLVM.Int.urem,LLVM.Int.icmp,LLVM.Int.select,LLVM.Int.fshl,LLVM.Int.fshr,hp,RuntimeValue.isRefinedBy,isRefinedBy,Id.run]
    | val c =>
      have hr : (c % BitVec.ofNat w w).toNat = c.toNat % w := by
        simp [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_two_pow_self]
      have hd : (BitVec.ofNat w w == 0) = false := by simpa [LLVM.Int.isUnsignedDivisionUB,BitVec.ofInt_natCast] using hub
      simp only [LLVM.Int.urem,Id.run,pure,BitVec.ofInt_ofNat,BitVec.ofInt_natCast,Int.ofNat_eq_natCast,hp]
      try simp only [hd, Bool.false_eq_true, reduceIte]
      first
      | have he := rotate_select_eq_zero false false x c _ hr; simp only at he; rw [he]
      | have he := rotate_select_eq_zero false true x c _ hr; simp only at he; rw [he]
      | have he := rotate_select_eq_zero true false x c _ hr; simp only at he; rw [he]
      | have he := rotate_select_eq_zero true true x c _ hr; simp only at he; rw [he]
      exact RuntimeValue.isRefinedBy_refl _
end Veir.InstSimplify
