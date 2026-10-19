import Veir.Passes.ArithCanonicalize.CastSupport

/-! Scalar integer instances of CommonFolders unary/cast poison propagation.
    VeIR materializes fully poisoned integer attributes as `llvm.mlir.poison`. -/
namespace Veir.ArithCanonicalize.G005

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.SelectSupport
  Veir.ArithCanonicalize.CastSupport

def extuiPattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let resultTy ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.matchNative (sourceTy, resultTy)
        (fun (sourceTy, resultTy) =>
          match sourceTy.cast? IntegerType, resultTy.cast? IntegerType with
          | some a, some b => a.bitwidth < b.bitwidth
          | _, _ => false)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[sourceTy]
      let _ ← MatchProg.root (.arith .extui) #[poison.res[0]!] #[resultTy]
      return (resultTy, poison.properties))
    (fun (resultTy, poisonProps) =>
      CreateProg.operation (.llvm .mlir__poison) #[] #[resultTy] poisonProps)
    (fun result => result)

theorem extuiValid : Pattern.Valid extuiPattern := by
  simp only [extuiPattern]
  provePuddleValid
  rintro ⟨a, sa⟩ ⟨b, sb⟩ pProps pVal hPoison rootProps result hResult hWidths
  cases pProps
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidths
  obtain rfl := (poison_iff a pVal).mp hPoison
  obtain rfl := (extui_iff a b hWidths rootProps .poison result).mp hResult
  refine ⟨.int b .poison, ?_, ?_⟩
  · exact (poison_iff b _).mpr rfl
  · simp [LLVM.Int.zext, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def extsiPattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let resultTy ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.matchNative (sourceTy, resultTy)
        (fun (sourceTy, resultTy) =>
          match sourceTy.cast? IntegerType, resultTy.cast? IntegerType with
          | some a, some b => a.bitwidth < b.bitwidth
          | _, _ => false)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[sourceTy]
      let _ ← MatchProg.root (.arith .extsi) #[poison.res[0]!] #[resultTy]
      return (resultTy, poison.properties))
    (fun (resultTy, poisonProps) =>
      CreateProg.operation (.llvm .mlir__poison) #[] #[resultTy] poisonProps)
    (fun result => result)

theorem extsiValid : Pattern.Valid extsiPattern := by
  simp only [extsiPattern]
  provePuddleValid
  rintro ⟨a, sa⟩ ⟨b, sb⟩ pProps pVal hPoison rootProps result hResult hWidths
  cases pProps
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidths
  obtain rfl := (poison_iff a pVal).mp hPoison
  obtain rfl := (extsi_iff a b hWidths .poison result).mp hResult
  refine ⟨.int b .poison, ?_, ?_⟩
  · exact (poison_iff b _).mpr rfl
  · simp [LLVM.Int.sext, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def trunciPattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let resultTy ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.matchNative (sourceTy, resultTy)
        (fun (sourceTy, resultTy) =>
          match sourceTy.cast? IntegerType, resultTy.cast? IntegerType with
          | some a, some b => b.bitwidth < a.bitwidth
          | _, _ => false)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[sourceTy]
      let _ ← MatchProg.root (.arith .trunci) #[poison.res[0]!] #[resultTy]
      return (resultTy, poison.properties))
    (fun (resultTy, poisonProps) =>
      CreateProg.operation (.llvm .mlir__poison) #[] #[resultTy] poisonProps)
    (fun result => result)

theorem trunciValid : Pattern.Valid trunciPattern := by
  simp only [trunciPattern]
  provePuddleValid
  rintro ⟨a, sa⟩ ⟨b, sb⟩ pProps pVal hPoison rootProps result hResult hWidths
  cases pProps
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidths
  obtain rfl := (poison_iff a pVal).mp hPoison
  obtain rfl := (trunci_iff b a hWidths rootProps .poison result).mp hResult
  refine ⟨.int b .poison, ?_, ?_⟩
  · exact (poison_iff b _).mpr rfl
  · simp [LLVM.Int.trunc, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.G005
