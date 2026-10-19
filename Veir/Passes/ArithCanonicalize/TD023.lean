import Veir.Passes.ArithCanonicalize.CmpCastSupport

/-! Pinned `CmpIExtSI`: eq/ne cmpi through two matching sign extensions. -/
namespace Veir.ArithCanonicalize.TD023

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport
open Veir.ArithCanonicalize.CastSupport
open Veir.ArithCanonicalize.CmpCastSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let narrow ← MatchProg.type (Attr := IntegerType)
      let wide ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      MatchProg.matchNative (narrow, wide) (fun (narrow, wide) =>
        match narrow.cast? IntegerType, wide.cast? IntegerType with
        | some n, some w => n.bitwidth < w.bitwidth
        | _, _ => false)
      let x ← MatchProg.value narrow
      let y ← MatchProg.value narrow
      let ex ← MatchProg.operation (.arith .extsi) #[x] #[wide]
      let ey ← MatchProg.operation (.arith .extsi) #[y] #[wide]
      let root ← MatchProg.root (.arith .cmpi)
        #[ex.res[0]!, ey.res[0]!] #[boolTy]
        (fun p => p.predicate == .eq || p.predicate == .ne)
      return (boolTy, x, y, root.properties))
    (fun (boolTy, x, y, props) =>
      CreateProg.operation (.arith .cmpi) #[x, y] #[boolTy] props)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  rintro ⟨a, sa⟩ ⟨b, sb⟩ boolTy ⟨cw, cs⟩ hTy hBool
    x hx y hy px vx hX py vy hY p v hPred hCmp hWidths
  cases hTy
  cases hBool
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType.mp hy
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidths
  obtain rfl := (extsi_iff a b hWidths x vx).mp hX
  obtain rfl := (extsi_iff a b hWidths y vy).mp hY
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hCmp
  refine ⟨.int 1 (LLVM.Int.icmp x y p.predicate), ?_, ?_⟩
  · exact (cmpi_iff _ _ _ _ _).mpr rfl
  · have hp : p.predicate = .eq ∨ p.predicate = .ne := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using hPred
    rw [icmp_sext_eq_ne p.predicate hp x y hWidths]
    exact RuntimeValue.isRefinedBy_refl _

end Veir.ArithCanonicalize.TD023
