import Veir.Passes.ArithCanonicalize.CmpCastSupport
import Veir.Passes.ArithCanonicalize.F084

/-! Pinned cmpi(ne, extsi(x:i1), 0) fold. -/
namespace Veir.ArithCanonicalize.F082

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport
open Veir.ArithCanonicalize.CastSupport
open Veir.ArithCanonicalize.CmpCastSupport

private theorem sext_zero (b : Nat) (hab : 1 < b) :
    LLVM.Int.sext (.val (0#1)) b hab = .val (0#b) := by
  have hz : (0#1).signExtend b = 0#b := by
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_signExtend_of_le (Nat.le_of_lt hab)]
    simp
  simp [LLVM.Int.sext, hz, Id.run]

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
      let ext ← MatchProg.operation (.arith .extsi) #[x] #[wide]
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
  obtain rfl := (extsi_iff 1 b hWidth x vx).mp hEx
  obtain rfl := (constant_iff _ _ _).mp hConst
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hCmp
  rw [hPred, hZero]
  change RuntimeValue.int 1
    (LLVM.Int.icmp (LLVM.Int.sext x b hWidth) (.val (0#b)) .ne) ⊒ .int 1 x
  rw [←sext_zero b hWidth,
    icmp_sext_eq_ne .ne (Or.inr rfl) x (.val (0#1)) hWidth]
  exact F084.ne_zero_refines x

end Veir.ArithCanonicalize.F082
