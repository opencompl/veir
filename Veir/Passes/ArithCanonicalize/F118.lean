import Veir.Passes.ArithCanonicalize.ExtremaSupport
import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned maxsi(x, intMin) fold. -/
namespace Veir.ArithCanonicalize.F118

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport
open Veir.ArithCanonicalize.ExtremaSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← MatchProg.operation (.arith .constant) #[] #[ty]
      MatchProg.matchNative (ty, c.properties) (fun (ty, p) =>
        (p.value.type : TypeAttr) == ty &&
          (BitVec.ofInt p.value.type.bitwidth p.value.value) ==
            BitVec.intMin p.value.type.bitwidth)
      let _ ← MatchProg.root (.arith .maxsi) #[x, c.res[0]!] #[ty]
      return x)
    pure
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  rintro ⟨w, s⟩ x hx cp cv hc p v hv hty hbits
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (maxsi_iff _ _ _ _).mp hv
  have htype : cp.value.type = IntegerType.mk w s := by grind
  rw [htype] at hbits
  simpa only [hbits] using maxsi_bottom x

end Veir.ArithCanonicalize.F118
