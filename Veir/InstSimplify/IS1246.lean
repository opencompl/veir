import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1246
private theorem rem_ones (x : BitVec w) (h : 0 < w) : x.srem (BitVec.allOnes w) = 0 := by
  have hm : (BitVec.allOnes w).msb = true := by simp [BitVec.msb_allOnes, h]
  rw [BitVec.srem_eq]
  simp only [hm]
  cases x.msb <;> simp [← BitVec.neg_one_eq_allOnes]

private theorem sext_one (w : Nat) (h : 1 < w) : BitVec.signExtend w (1#1) = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend]
private theorem sext_srem_refines (b : LLVM.Int 1) (x : LLVM.Int w) (h : 1 < w)  :
    RuntimeValue.int w (LLVM.Int.srem x (LLVM.Int.sext b w h)) ⊒ .int w (.val 0) := by
  cases b with
  | poison => cases x <;> simp [LLVM.Int.sext, LLVM.Int.srem, sext_one w h, rem_ones _ (show 0 < w by omega), Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val b =>
    rcases BitVec.eq_zero_or_eq_one b with rfl | rfl
    · cases x <;> simp [LLVM.Int.sext, LLVM.Int.srem, sext_one w h, rem_ones _ (show 0 < w by omega), Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      grind
    · cases x <;> simp [LLVM.Int.sext, LLVM.Int.srem, sext_one w h, rem_ones _ (show 0 < w by omega), Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      grind

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sty ← MatchProg.type (Attr := IntegerType)
      let ty ← MatchProg.type (Attr := IntegerType)
      let b ← MatchProg.value sty
      let x ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .sext) #[b] #[ty]
      let _ ← MatchProg.root (.llvm .srem) #[x,sh.res[0]!] #[ty]
      MatchProg.matchNative sty (fun t => match t.val with
        | .integerType it => it.bitwidth == 1
        | _ => false)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨sw,ss⟩ ⟨w,s⟩ b x sp sv hs p v hi hw
  have hsw : sw = 1 := by
    change (sw == 1) = true at hw
    simpa using hw
  subst sw
  have hlt := sext_width_lt _ _ sp b sv hs
  obtain rfl := (sext_iff _ _ sp b sv hlt).mp hs
  obtain ⟨hu,rfl⟩ := (srem_iff w p x _ v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · exact sext_srem_refines _ _ _
end Veir.InstSimplify.IS1246
