import Veir.Passes.ArithCanonicalize.ConstSupport
import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned cmpi(x,x) folds, partitioned by the predicate's equality truth value. -/
namespace Veir.ArithCanonicalize.F081

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport

private theorem cmp_self_truth (p : LLVM.IntPred) (x : BitVec w) :
    LLVM.IntPred.eval p x x = LLVM.IntPred.eval p (0#1) (0#1) := by
  cases p <;> simp [LLVM.IntPred.eval, BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule]

private theorem cmp_self_refines (p : LLVM.IntPred) (x : LLVM.Int w) :
    RuntimeValue.int 1 (LLVM.Int.icmp x x p) ⊒
      .int 1 (.val (BitVec.ofBool (LLVM.IntPred.eval p (0#1) (0#1)))) := by
  cases x with
  | poison => simp [LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.icmp, cmp_self_truth, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def pattern_true : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .cmpi) #[x, x] #[boolTy]
        (fun p => LLVM.IntPred.eval p.predicate (0#1) (0#1))
      return boolTy)
    (fun boolTy => createConstant boolTy 1)
    (fun result => result)

def pattern_false : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .cmpi) #[x, x] #[boolTy]
        (fun p => !LLVM.IntPred.eval p.predicate (0#1) (0#1))
      return boolTy)
    (fun boolTy => createConstant boolTy 0)
    (fun result => result)

theorem pattern_true_valid : Pattern.Valid pattern_true := by
  simp only [pattern_true, createConstant]
  provePuddleValid
  rintro ⟨w, s⟩ ty ⟨bw, bs⟩ hTy hBool x hx p v hTruth hCmp
  cases hTy
  cases hBool
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hCmp
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int 1 (.val (1#1)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    exact congrArg (fun bits => RuntimeValue.int 1 (.val bits))
      (ofInt_ofInt (IntegerType.signless 1) 1).symm
  · have h := cmp_self_refines p.predicate x
    simp [hTruth] at h
    exact h

theorem pattern_false_valid : Pattern.Valid pattern_false := by
  simp only [pattern_false, createConstant]
  provePuddleValid
  rintro ⟨w, s⟩ ty ⟨bw, bs⟩ hTy hBool x hx p v hTruth hCmp
  cases hTy
  cases hBool
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hCmp
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int 1 (.val (0#1)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    exact congrArg (fun bits => RuntimeValue.int 1 (.val bits))
      (ofInt_ofInt (IntegerType.signless 1) 0).symm
  · have h := cmp_self_refines p.predicate x
    simp [hTruth] at h
    exact h

end Veir.ArithCanonicalize.F081
