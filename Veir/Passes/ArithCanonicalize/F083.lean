import Veir.Passes.ArithCanonicalize.CmpCastSupport
import Veir.Passes.ArithCanonicalize.F084

/-! Pinned cmpi(ne, extui(x:i1), 0) fold. -/
namespace Veir.ArithCanonicalize.F083

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport
open Veir.ArithCanonicalize.CastSupport
open Veir.ArithCanonicalize.CmpCastSupport

private theorem zext_zero (b : Nat) (hab : 1 < b) :
    LLVM.Int.zext (.val (0#1)) b false hab = .val (0#b) := by
  have hz : (0#1).zeroExtend b = 0#b := by
    simp
  simp [LLVM.Int.zext, hz, Id.run]

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let boolTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let wide ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative wide (fun wide =>
        match wide.cast? IntegerType with
        | some ty => 1 < ty.bitwidth
        | none => false)
      let x ← MatchProg.value boolTy
      let ext ← MatchProg.operation (.arith .extui) #[x] #[wide]
      let zero ← matchConstant wide 0
      let _ ← MatchProg.root (.arith .cmpi) #[ext.res[0]!, zero] #[boolTy]
        (fun p => p.predicate == .ne)
      return x)
    pure
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  rintro boolTy ⟨aw, as⟩ hTy hBool ⟨b, s⟩ x hx
    px vx hEx cp cv hZero hConst p v hPred hCmp hWidth
  cases hTy
  cases hBool
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidth
  obtain rfl := (extui_iff 1 b hWidth px x vx).mp hEx
  obtain rfl := (constant_iff _ _ _).mp hConst
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hCmp
  rw [hPred, hZero]
  change RuntimeValue.int 1
    (LLVM.Int.icmp (LLVM.Int.zext x b px.nneg hWidth) (.val (0#b)) .ne) ⊒ .int 1 x
  rw [←zext_zero b hWidth]
  exact RuntimeValue.isRefinedBy_trans
    (icmp_zext_eq_ne_refines .ne (Or.inr rfl) x (.val (0#1)) hWidth px.nneg false)
    (F084.ne_zero_refines x)

end Veir.ArithCanonicalize.F083
