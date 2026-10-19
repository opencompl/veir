import Veir.Passes.ArithCanonicalize.CmpSupport

/-! Pinned `XOrINotCmpI`: invert the cmpi predicate under i1 xor true. -/
namespace Veir.ArithCanonicalize.TD020

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport
open Veir.ArithCanonicalize.CmpSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let cmp ← MatchProg.operation (.arith .cmpi) #[a, b] #[boolTy]
      let one ← matchConstant boolTy 1
      let _ ← MatchProg.root (.arith .xori) #[cmp.res[0]!, one] #[boolTy]
      return (boolTy, a, b, cmp.properties))
    (fun (boolTy, a, b, props) => do
      let inverted ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.arith .cmpi))) props
        (fun p => some { predicate := invert p.predicate })
      CreateProg.operation (.arith .cmpi) #[a, b] #[boolTy] inverted)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  rintro ⟨w, s⟩ ty ⟨bw, bs⟩ hTy hBool a ha b hb
    cp cmpVal hCmp oneProp oneVal hOne hConst xp result hXor
  cases hTy
  cases hBool
  obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp ha
  obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hb
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hCmp
  obtain rfl := (constant_iff _ _ _).mp hConst
  obtain rfl := (xori_iff _ _ _ _).mp hXor
  refine ⟨.int 1 (LLVM.Int.icmp a b (invert cp.predicate)), ?_, ?_⟩
  · exact (cmpi_iff _ _ _ _ _).mpr rfl
  · rw [hOne]
    change RuntimeValue.int 1 (LLVM.Int.xor (LLVM.Int.icmp a b cp.predicate)
      (.val (1#1))) ⊒
      .int 1 (LLVM.Int.icmp a b (invert cp.predicate))
    rw [xor_icmp_invert]
    exact RuntimeValue.isRefinedBy_refl _

end Veir.ArithCanonicalize.TD020
