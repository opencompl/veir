import Veir.Passes.ArithCanonicalize.TD015Support
import Veir.Passes.ArithCanonicalize.ConstSupport

namespace Veir.ArithCanonicalize.TD015

open Veir Veir.Puddle Veir.Data
open Veir.ArithPuddle

/-- Scalar instance of upstream `subi(subi(x,y),x) → subi(0,y)`, retaining
    the identity of the repeated SSA value and intersecting overflow flags. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let inner ← MatchProg.operation (.arith .subi) #[x, y] #[ty]
      let root ← MatchProg.root (.arith .subi) #[inner.res[0]!, x] #[ty]
      return (ty, y, inner.properties, root.properties))
    (fun (ty, y, p0, p1) => do
      let zero ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.arith .constant))) ty (fun ty => do
        let some intTy := ty.cast? IntegerType | none
        some { value := IntegerAttr.ofInt 0 intTy })
      let c ← CreateProg.operation (.arith .constant) #[] #[ty] zero
      let flags ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.arith .subi))) (p0, p1) (fun (p0, p1) =>
        some { attr := { nsw := p0.attr.nsw && p1.attr.nsw,
                         nuw := p0.attr.nuw && p1.attr.nuw } })
      let replacement ← CreateProg.operation (.arith .subi) #[c.res[0]!, y] #[ty] flags
      return replacement)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [IsTypeAttr.cast?_of]
  rintro ⟨w, s⟩ x hx y hy p0 mid hInner p1 out hOuter
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType.mp hy
  obtain rfl := (subi_iff _ _ _ _ _).mp hInner
  obtain rfl := (subi_iff _ _ _ _ _).mp hOuter
  refine ⟨.int w (.val (0#w)), ?_,
    .int w (LLVM.Int.sub (.val (0#w)) y
      (p0.attr.nsw && p1.attr.nsw) (p0.attr.nuw && p1.attr.nuw)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    exact congrArg (fun bits => RuntimeValue.int w (.val bits))
      (ofInt_ofInt (IntegerType.mk w s) 0).symm
  · exact (subi_iff _ _ _ _ _).mpr rfl
  · exact sub_sub_flagged_refines w x y
      p0.attr.nsw p0.attr.nuw p1.attr.nsw p1.attr.nuw

end Veir.ArithCanonicalize.TD015
