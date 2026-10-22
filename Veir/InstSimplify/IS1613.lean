import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1613

private theorem flip_compare (x y : LLVM.Int w) : LLVM.Int.icmp y x .ule = LLVM.Int.icmp x y .uge := by
  cases x <;> cases y <;> rfl

private theorem lt_iff_not_ge (a b : Nat) : a < b ↔ ¬b ≤ a := by omega

def pattern_or (flipped commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let z ← matchBitConstant ty 0
    let c0 ← MatchProg.operation (.llvm .icmp) (cond flipped #[y,x] #[x,y]) #[bt] (fun p => p.predicate == (cond flipped .ule .uge))
    let c1 ← MatchProg.operation (.llvm .icmp) #[y,z] #[bt] (fun p => p.predicate == .ne)
    let _ ← MatchProg.root (.llvm .or) (cond commute #[c1.res[0]!,c0.res[0]!] #[c0.res[0]!,c1.res[0]!]) #[bt]
    MatchProg.matchNative bt (fun bt => match bt.val with | .integerType t => t.bitwidth == 1 | _ => false)
    return bt)
  (fun bt => do
    let p ← CreateProg.applyNative bt (fun bt => match bt.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt 1 t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[bt] p
    return c.res[0]!) (fun x => x)

theorem semantic_or (w : Nat) (x y : LLVM.Int w) (d : Bool) :
    RuntimeValue.int 1 (LLVM.Int.or (LLVM.Int.icmp x y .uge)
      (LLVM.Int.icmp y (.val 0) .ne) d) ⊒ .int 1 (.val (BitVec.ofInt 1 1)) := by
  cases x with
  | poison => cases y <;> simp [LLVM.Int.icmp, LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
    | val y =>
      cases h0 : x.ult y <;> cases h1 : y == 0 <;> cases d <;>
        simp_all [LLVM.Int.icmp, LLVM.Int.or, LLVM.IntPred.eval, RuntimeValue.isRefinedBy, isRefinedBy,
          Id.run, pure, BitVec.ofBool, BitVec.ult, BitVec.ule, bitvec_zero_test, lt_iff_not_ge, -Nat.not_le] <;> omega

theorem valid_or (flipped commute : Bool) : Pattern.Valid (pattern_or flipped commute) := by
  cases flipped <;> cases commute
  all_goals
    simp only [pattern_or, matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ ⟨bw,bs⟩ x y zp zv hi
    intro cp0 cv0 hp0 hi0 cp1 cv1 hp1 hi1 rp rv hir hz hb
    have hbw : bw = 1 := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hb
    subst bw
    obtain rfl := matched_bit_constant_eq _ _ 0 _ hi hz
    obtain rfl := (logic_icmp_iff _ _ _ _ _).mp hi0
    obtain rfl := (logic_icmp_iff _ _ _ _ _).mp hi1
    obtain rfl := (or_iff _ _ _ _ _).mp hir
    try simp only [beq_iff_eq] at hp0 hp1
    refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by cases bs <;> decide)
    · simpa [hp0,hp1,cond,flip_compare,logic_and_comm,logic_or_comm] using semantic_or w x y rp.disjoint

end Veir.InstSimplify.IS1613
