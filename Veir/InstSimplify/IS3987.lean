import Veir.InstSimplify.CastLogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS3987
def pred (signed : Bool) : LLVM.IntPred := cond signed .slt .ugt
def pattern (signed flipped : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType)
    let dst ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value src
    let z ← MatchProg.operation (.llvm .zext) #[x] #[dst]
    let s ← MatchProg.operation (.llvm .sext) #[x] #[dst]
    let _ ← MatchProg.root (.llvm .icmp) (cond flipped #[s.res[0]!,z.res[0]!] #[z.res[0]!,s.res[0]!]) #[bt]
      (fun p => p.predicate == cond flipped (swapCmpPred (pred signed)) (pred signed))
    MatchProg.matchNative bt (fun bt => match bt.val with | .integerType t => t.bitwidth == 1 | _ => false)
    return bt)
  (fun bt => do
    let p ← CreateProg.applyNative bt (fun bt => match bt.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt 0 t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[bt] p
    return c.res[0]!) (fun x => x)

theorem semantic (w v : Nat) (x : LLVM.Int w) (nneg signed : Bool) (hw : w < v) :
    RuntimeValue.int 1 (LLVM.Int.icmp (LLVM.Int.zext x v nneg hw) (LLVM.Int.sext x v hw) (pred signed)) ⊒
      .int 1 (.val (BitVec.ofInt 1 0)) := by
  cases x with
  | poison => simp [LLVM.Int.icmp,LLVM.Int.zext,LLVM.Int.sext,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val x =>
    have hu := subset_toNat_le (x.zeroExtend v) (x.signExtend v) (logic_zext_and_sext x v)
    have hs : (x.signExtend v).toInt ≤ (x.zeroExtend v).toInt := by
      rw [BitVec.toInt_signExtend_of_le (by omega),logic_zext_toInt x hw,BitVec.toInt_eq_toNat_cond]
      split <;> omega
    rcases logic_zext_outcomes x v nneg hw with hz | hz
    · simp [hz,LLVM.Int.icmp,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
    · cases signed <;>
        simp_all [hz,LLVM.Int.sext,LLVM.Int.icmp,pred,cond,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy,
          LLVM.IntPred.eval,BitVec.ult,BitVec.ule,BitVec.slt,BitVec.sle,hu,hs,Nat.not_lt_of_ge hu,Int.not_lt_of_ge hs]

theorem valid (signed flipped : Bool) : Pattern.Valid (pattern signed flipped) := by
  cases flipped
  all_goals
    simp only [pattern]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,ss⟩ ⟨v,ds⟩ ⟨bw,bs⟩ x zp zv hz sp sv hs rp rv hp hr hb
    have hb : bw = 1 := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hb
    subst bw
    have hw := logic_zext_width_lt _ _ _ _ _ hz
    obtain rfl := (logic_zext_iff _ _ _ _ _ hw).mp hz
    obtain rfl := (sext_iff _ _ _ _ _ hw).mp hs
    obtain rfl := (logic_icmp_iff _ _ _ _ _).mp hr
    refine ⟨.int 1 (.val (BitVec.ofInt 1 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _ rfl _).mpr
      exact congrArg (fun b => RuntimeValue.int 1 (.val b)) (integerAttr_bits ⟨1,bs⟩ 0).symm
    · simpa [hp,cond,logic_icmp_swap] using semantic w v x zp.nneg signed hw
end Veir.InstSimplify.IS3987
