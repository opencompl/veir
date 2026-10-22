import Veir.InstSimplify.LogicExtra
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2515
def pattern (c : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let c0 ← matchBitConstant ty c
    let c1 ← matchBitConstant ty (-c-1)
    let x ← MatchProg.operation (.llvm .xor) #[a,c0] #[ty]
    let y ← MatchProg.operation (.llvm .xor) #[a,c1] #[ty]
    let _ ← MatchProg.root (.llvm .or) #[x.res[0]!,y.res[0]!] #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.applyNative ty (fun ty => match ty.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt (-1) t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p
    return c.res[0]!) (fun x => x)

theorem semantic (w : Nat) (a : LLVM.Int w) (c : BitVec w) (d : Bool) :
    RuntimeValue.int w (LLVM.Int.or (LLVM.Int.xor a (.val c))
      (LLVM.Int.xor a (.val (~~~c))) d) ⊒ .int w (.val (BitVec.ofInt w (-1))) := by
  cases a with
  | poison => simp [LLVM.Int.xor, LLVM.Int.or, Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val a =>
    simp only [LLVM.Int.xor,LLVM.Int.or,Id.run,pure]
    all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy,isRefinedBy,const_negOne])
    all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy,isRefinedBy,const_negOne])
    all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy,isRefinedBy,const_negOne])
    all_goals try simp [RuntimeValue.isRefinedBy,isRefinedBy,const_negOne]
    all_goals
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [hi]
      try grind only

theorem valid (c : Int) : Pattern.Valid (pattern c) := by
  simp only [pattern,matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a p0 v0 hi0 p1 v1 hi1 xp xv hxi yp yv hyi rp rv hri hc0 hc1
  obtain rfl := matched_bit_constant_eq _ _ c _ hi0 hc0
  obtain rfl := matched_bit_constant_eq _ _ (-c-1) _ hi1 hc1
  obtain rfl := (xor_iff _ _ _ _ _).mp hxi
  obtain rfl := (xor_iff _ _ _ _ _).mp hyi
  obtain rfl := (or_iff _ _ _ _ _).mp hri
  refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
  · apply (constant_iff _ _ _ rfl _).mpr
    exact congrArg (fun b => RuntimeValue.int w (.val b)) (integerAttr_bits ⟨w,s⟩ (-1)).symm
  · simpa only [ofInt_complement] using semantic w a (BitVec.ofInt w c) rp.disjoint
end Veir.InstSimplify.IS2515
