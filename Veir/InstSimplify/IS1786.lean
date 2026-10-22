import Veir.InstSimplify.AddCompareSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1786
/-- Exact pinned-source positive/nonzero constant and modular delta guards. -/
def pattern (k0 k1 : Int) (commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let c ← matchBitConstant ty k0
    let d ← matchBitConstant ty k1
    let sum ← MatchProg.operation (.llvm .add) #[a,c] #[ty] (fun p => p.nuw)
    let p ← MatchProg.operation (.llvm .icmp) #[sum.res[0]!,d] #[bt] (fun p => p.predicate == .uge)
    let q ← MatchProg.operation (.llvm .icmp) #[a,c] #[bt] (fun p => p.predicate == .ule)
    let _ ← MatchProg.root (.llvm .or) (cond commute #[q.res[0]!,p.res[0]!] #[p.res[0]!,q.res[0]!]) #[bt]
    MatchProg.matchNative (ty,bt) (fun (ty,bt) => match ty.val,bt.val with
      | .integerType t,.integerType b => (b.bitwidth == 1) && (decide ((BitVec.ofInt t.bitwidth k0) ≠ 0) &&
          ((BitVec.ofInt t.bitwidth k1 - BitVec.ofInt t.bitwidth k0).toNat == 2))
      | _,_ => false)
    return bt)
  (fun bt => do
    let p ← CreateProg.applyNative bt (fun bt => match bt.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt 1 t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[bt] p
    return c.res[0]!) (fun x => x)

theorem semantic (w : Nat) (a : LLVM.Int w) (c d : BitVec w) (nsw nuw disjoint : Bool)
    (hc : c ≠ 0) (hd : (d-c).toNat = 2) (hf : nuw = true) :
    RuntimeValue.int 1 (LLVM.Int.or
      (LLVM.Int.icmp (LLVM.Int.add a (.val c) nsw nuw) (.val d) .uge)
      (LLVM.Int.icmp a (.val c) .ule) disjoint) ⊒ .int 1 (.val (BitVec.ofInt 1 1)) := by
  cases a with
  | poison => simp [LLVM.Int.add,LLVM.Int.icmp,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val a =>
    rcases add_outcomes a c nsw nuw with hadd | hadd
    · simp [hadd,LLVM.Int.icmp,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
    · have facts := logic_add_value_facts a c (a+c) nsw nuw hadd
      have hbad : ¬(LLVM.IntPred.eval .uge (a+c) d = false ∧ LLVM.IntPred.eval .ule a c = false) := by
        rintro ⟨h0,h1⟩
        simp [LLVM.IntPred.eval,BitVec.ult,BitVec.ule,BitVec.slt,BitVec.sle] at h0 h1
        have bounds := logic_addcmp_unsigned a c d 2 hc h1 hd (facts.2.2 hf)
        simp only [BitVec.toNat_add,BitVec.toInt_add] at bounds
        omega
      cases h0 : LLVM.IntPred.eval .uge (a+c) d <;>
        cases h1 : LLVM.IntPred.eval .ule a c <;> cases disjoint
      all_goals simp_all only [Bool.false_eq_true,true_and,false_and,not_true_eq_false]
      all_goals simp only [hadd,LLVM.Int.icmp,Id.run,pure,h0,h1]
      all_goals simp [LLVM.Int.or,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure]

theorem valid (k0 k1 : Int) (commute : Bool) : Pattern.Valid (pattern k0 k1 commute) := by
  cases commute
  all_goals
    simp only [pattern,matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,ss⟩ ⟨bw,bs⟩ a cprop cv hci dprop dv hdi ap av hflag hai pp pv hpp hpi qp qv hqp hqi rp rv hri hcg hdg hg
    have hg : bw = 1 ∧ (BitVec.ofInt w k0 ≠ 0) ∧
        (BitVec.ofInt w k1 - BitVec.ofInt w k0).toNat = 2 := by
      simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hg
    obtain ⟨rfl,hc,hd⟩ := hg
    obtain rfl := matched_bit_constant_eq _ _ k0 _ hci hcg
    obtain rfl := matched_bit_constant_eq _ _ k1 _ hdi hdg
    obtain rfl := (add_iff _ _ _ _ _).mp hai
    obtain rfl := (logic_icmp_iff _ _ _ _ _).mp hpi
    obtain rfl := (logic_icmp_iff _ _ _ _ _).mp hqi
    obtain rfl := (or_iff _ _ _ _ _).mp hri
    refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
    · apply (constant_iff _ _ _ rfl _).mpr
      exact congrArg (fun b => RuntimeValue.int 1 (.val b)) (integerAttr_bits ⟨1,bs⟩ 1).symm
    · simpa [hpp,hqp,logic_and_comm,logic_or_comm] using semantic w a (BitVec.ofInt w k0) (BitVec.ofInt w k1) ap.nsw ap.nuw rp.disjoint hc hd hflag
end Veir.InstSimplify.IS1786
