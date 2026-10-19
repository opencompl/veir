import Veir.Passes.ArithCanonicalize.CastSupport
import Veir.Passes.ArithCanonicalize.TD017Support
import Veir.Passes.ArithCanonicalize.ConstSupport

/-! Upstream `mulsi_extended(x, strictly positive 1) -> (x, extsi(cmpi slt x, 0))`. -/
namespace Veir.ArithCanonicalize.TD017

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize.CastSupport
  Veir.ArithCanonicalize.SelectSupport
  Veir.ArithCanonicalize.ExtendedSupport
  Veir.ArithCanonicalize.TD017Support

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => 1 < t.bitwidth)
      let x ← MatchProg.value ty
      let one ← matchConstant ty 1
      let _ ← MatchProg.root (.arith .mulsi_extended) #[x, one] #[ty, ty]
      return (ty, x))
    (fun (ty, x) => do
      let boolTy ← CreateProg.type (IntegerType.signless 1)
      let zero ← createConstant ty 0
      let cmpProps ← CreateProg.property (.arith .cmpi) { predicate := .slt }
      let cmp ← CreateProg.operation (.arith .cmpi) #[x, zero] #[boolTy] cmpProps
      let extProps ← CreateProg.property (.arith .extsi) ()
      let high ← CreateProg.operation (.arith .extsi) #[cmp.res[0]!] #[ty] extProps
      return (x, high.res[0]!))
    (fun (low, high) => #[low, high])

theorem valid : Pattern.Valid pattern := by
  unfold pattern matchConstant createConstant
  provePuddleValid
  rintro ty ⟨w, s⟩ rfl hw x hx c vc hOne hConst
    rootProp r0 r1 hRoot
  obtain ⟨xv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hConst
  obtain ⟨rfl, rfl⟩ := (mulsi_extended_iff _ _ _ _ _).mp hRoot
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val (0#w)), ?_,
    .int 1 (LLVM.Int.icmp xv (.val (0#w)) .slt), ?_,
    .int w (LLVM.Int.sext (LLVM.Int.icmp xv (.val (0#w)) .slt) w (by omega)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    exact congrArg (fun bits => RuntimeValue.int w (.val bits))
      (Veir.ArithCanonicalize.ofInt_ofInt (IntegerType.mk w s) 0).symm
  · exact (cmpi_iff w { predicate := .slt } xv (.val (0#w)) _).mpr rfl
  · exact (extsi_iff 1 w hw _ _).mpr rfl
  · rw [hOne]
    simpa using smul_one_refines xv hw

end Veir.ArithCanonicalize.TD017
