import Veir.InstSimplify.CastLogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1534

def pattern_or (reversed flipped commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let z ← matchBitConstant ty 0
    let dif ← MatchProg.operation (.llvm .sub) #[a,b] #[ty]
    let zc ← MatchProg.operation (.llvm .icmp) #[dif.res[0]!,z] #[bt] (fun p => p.predicate == .ne)
    let uc ← MatchProg.operation (.llvm .icmp) (cond flipped #[b,a] #[a,b]) #[bt] (fun p => p.predicate == cond flipped (swapCmpPred (cond reversed .uge .ule)) (cond reversed .uge .ule))
    let _ ← MatchProg.root (.llvm .or) (cond commute #[uc.res[0]!,zc.res[0]!] #[zc.res[0]!,uc.res[0]!]) #[bt]
    MatchProg.matchNative bt (fun bt => match bt.val with | .integerType t => t.bitwidth == 1 | _ => false)
    return bt)
  (fun bt => do
    let p ← CreateProg.applyNative bt (fun bt => match bt.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt 1 t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[bt] p
    return c.res[0]!) (fun x => x)

theorem semantic_or (w : Nat) (a b : LLVM.Int w) (nsw nuw d reversed : Bool) :
    RuntimeValue.int 1 (LLVM.Int.or
      (LLVM.Int.icmp (LLVM.Int.sub a b nsw nuw) (.val 0) .ne)
      (LLVM.Int.icmp a b (cond reversed .uge .ule)) d) ⊒ .int 1 (.val (BitVec.ofInt 1 1)) := by
  cases a with
  | poison => cases b <;> simp [LLVM.Int.sub,LLVM.Int.icmp,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val a =>
    cases b with
    | poison => simp [LLVM.Int.sub,LLVM.Int.icmp,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
    | val b =>
      rcases sub_outcomes a b nsw nuw with hs | hs
      · cases reversed <;> simp [hs,LLVM.Int.icmp,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
      · by_cases hab : a = b
        · subst b
          cases reversed <;> cases d <;> simp [hs,LLVM.Int.icmp,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy,LLVM.IntPred.eval,BitVec.ule,BitVec.ult,bne_eq]
        · have hsub : a - b ≠ 0 := by simpa [BitVec.sub_eq_iff_eq_add] using hab
          have hbeq : (a - b == 0) = false := by
            cases hz : (a - b == 0)
            · rfl
            · exact False.elim (hsub ((beq_iff_eq).mp hz))
          cases reversed <;> cases h0 : a.ult b <;> cases h1 : b.ult a <;> cases h2 : a.ule b <;> cases h3 : b.ule a <;> cases d <;>
            simp only [hs,LLVM.Int.icmp,LLVM.IntPred.eval,Id.run,pure,cond,bne_eq,hbeq,h0,h1,h2,h3] <;>
            simp [LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]

theorem valid_or (reversed flipped commute : Bool) : Pattern.Valid (pattern_or reversed flipped commute) := by
  cases reversed <;> cases flipped <;> cases commute
  all_goals
    simp only [pattern_or,matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ ⟨bw,bs⟩ a b zp zv hzi dp dv hdi zcp zcv hzp hzci ucp ucv hup huci rp rv hri hz hb
    have hbw : bw = 1 := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hb
    subst bw
    obtain rfl := matched_bit_constant_eq _ _ 0 _ hzi hz
    obtain rfl := (sub_iff _ _ _ _ _).mp hdi
    obtain rfl := (logic_icmp_iff _ _ _ _ _).mp hzci
    obtain rfl := (logic_icmp_iff _ _ _ _ _).mp huci
    obtain rfl := (or_iff _ _ _ _ _).mp hri
    refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
    · apply (constant_iff _ _ _ rfl _).mpr
      exact congrArg (fun b => RuntimeValue.int 1 (.val b)) (integerAttr_bits ⟨1,bs⟩ 1).symm
    · first
      | simpa [hzp,hup,cond,logic_and_comm,logic_or_comm,logic_icmp_swap] using semantic_or w a b dp.nsw dp.nuw rp.disjoint false
      | simpa [hzp,hup,cond,logic_and_comm,logic_or_comm,logic_icmp_swap] using semantic_or w a b dp.nsw dp.nuw rp.disjoint true
end Veir.InstSimplify.IS1534
