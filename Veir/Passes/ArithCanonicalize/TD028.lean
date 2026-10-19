import Veir.Passes.ArithCanonicalize.ConstSupport
import Veir.Passes.ArithCanonicalize.SelectMinMaxSupport

/-! Pinned `SelectI1ToNot`: `select(pred, false, true) → xori(pred, true)`. -/
namespace Veir.ArithCanonicalize.TD028

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let pred ← MatchProg.value boolTy
      let zero ← MatchProg.operation (.arith .constant) #[] #[boolTy]
      let one ← MatchProg.operation (.arith .constant) #[] #[boolTy]
      MatchProg.matchNative (zero.properties, one.properties)
        (fun (p0, p1) => p0.value.value == 0 && p1.value.value == 1)
      let _ ← MatchProg.root (.arith .select)
        #[pred, zero.res[0]!, one.res[0]!] #[boolTy]
      return (boolTy, pred))
    (fun (boolTy, pred) => do
      let one ← createConstant boolTy 1
      let props ← CreateProg.property (.arith .xori) ()
      CreateProg.operation (.arith .xori) #[pred, one] #[boolTy] props)
    (fun result => result)

theorem select_false_true_refines (c : LLVM.Int 1) :
    RuntimeValue.int 1 (LLVM.Int.select c (.val (0#1)) (.val (1#1))) ⊒
      .int 1 (LLVM.Int.xor c (.val (1#1))) := by
  cases c with
  | poison => simp [LLVM.Int.select, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have h : v = 0#1 ∨ v = 1#1 := by bv_decide
    rcases h with h | h <;> subst v <;>
      simp [LLVM.Int.select, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem pattern_valid : Pattern.Valid pattern := by
  unfold pattern createConstant
  provePuddleValid
  rintro ty ⟨w, sign⟩ rfl hWidth c hConforms p0 v0 h0Interp
    p1 v1 h1Interp p2 v2 hSelect h0 h1
  obtain ⟨c, rfl⟩ := RuntimeValue.Conforms.integerType.mp hConforms
  dsimp at hWidth
  subst w
  obtain rfl := (constant_iff _ _ _).mp h0Interp
  obtain rfl := (constant_iff _ _ _).mp h1Interp
  obtain rfl := (select_iff _ _ _ _ _).mp hSelect
  have hcast : (TypeAttr.of IntegerType (IntegerType.mk 1 sign)).cast? IntegerType =
      some (IntegerType.mk 1 sign) := by rfl
  simp only [hcast]
  refine ⟨.int 1 (.val (BitVec.ofInt 1 (IntegerAttr.ofInt 1
      (IntegerType.mk 1 sign)).value)), ?_,
    .int 1 (LLVM.Int.xor c (.val (BitVec.ofInt 1 (IntegerAttr.ofInt 1
      (IntegerType.mk 1 sign)).value))), ?_, ?_⟩
  · exact (constant_iff _ _ _).mpr rfl
  · exact (xori_iff _ _ _ _).mpr rfl
  · have hv : BitVec.ofInt 1 (IntegerAttr.ofInt 1 (IntegerType.mk 1 sign)).value = 1#1 := by
      simpa using ofInt_ofInt (IntegerType.mk 1 sign) 1
    simp only [h0, h1, hv]
    exact select_false_true_refines c

end Veir.ArithCanonicalize.TD028
