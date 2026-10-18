module

public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NegatePoison

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM


private theorem poison_iff {signedness : IntegerType.Signedness} (w : Nat)
    (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__poison) () #[IntegerType.mk w signedness]
      #[] #[v] ↔ v = .int w .poison := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk w signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk w signedness)) := by
    rfl
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val,
      Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
      List.cons.injEq, and_true] at hv
    simpa only [mlir_poison_eq] using hv.symm
  · rintro rfl
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val,
        mlir_poison_eq, Interp.pure_eq]


private def isZeroConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer attr => attr.value = 0
  | _ => false

/-- Scalar poison specialization of InstCombineNegator.cpp:111-114:
    `sub 0, poison -> poison`. The source `m_Undef` matcher also accepts true
    undef and aggregate/vector forms, which are outside this scalar pattern. -/
public def negatePoison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let zeroOp ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isZeroConstant
    let zero := zeroOp.res[0]!
    let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .sub) #[zero, poison.res[0]!] #[ty]
      (fun _ => true)
    return poison.res[0]!)
  pure
  (fun poison => poison)

public theorem negatePoison_valid : Pattern.Valid negatePoison := by
  simp only [negatePoison]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpPuddleSemantics
  rintro ⟨w, signedness⟩
  rintro ⟨constantValue⟩ zero hZero hInterpZero
  cases constantValue with
  | float _ | dense _ | string _ =>
    change false = true at hZero
    contradiction
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := by
      simpa [isZeroConstant] using of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro ⟨⟩ poison hPoison
    obtain rfl := (poison_iff (signedness := signedness) w _).mp hPoison
    rintro subProps result hResult
    obtain rfl := (sub_iff _ _ _ _ _).mp hResult
    rw [hZeroValue]
    rw [zero_sub_poison]
    exact RuntimeValue.isRefinedBy_refl _

end Veir.Passes.InstCombineLLVM.NegatePoison
