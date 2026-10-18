module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Data.LLVM.Int.Basic

namespace Veir.Passes.InstCombineLLVM.NegateIncrement

open Veir
open Veir.Data
open Veir.Puddle
open Veir.Passes.InstCombineLLVM

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

/-- Scalar specialization of InstCombineNegator.cpp:154-158: `-(x + 1) -> ~x`. -/
public def negateIncrement : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let one ← matchIntConstant ty 1
      let increment ← MatchProg.operation (.llvm .add) #[x, one] #[ty] (fun _ => true)
      let zero ← matchIntConstant ty 0
      let _ ← MatchProg.root (.llvm .sub) #[zero, increment.res[0]!] #[ty] (fun _ => true)
      return (ty, x))
    (fun (ty, x) => do
      let minusOneProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty fun type => do
          let some intType := type.cast? IntegerType | none
          return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-1) intType))
      let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] minusOneProps
      let xorProps ← CreateProg.property (.llvm .xor) ()
      let result ← CreateProg.operation (.llvm .xor) #[x, minusOne.res[0]!] #[ty] xorProps
      return result)
    (fun result => result.res[0]!)

public theorem negateIncrement_valid : Pattern.Valid negateIncrement := by
  simp only [negateIncrement, matchIntConstant]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
    forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x
  rintro ⟨oneValue⟩ one hOne hinterpOne
  cases oneValue with
  | float _ | dense _ | string _ => simp at hOne
  | integer oneAttr =>
    have hOneValue : oneAttr.value = 1 := of_decide_eq_true hOne
    obtain rfl := (constant_iff _ oneAttr _).mp hinterpOne
    rintro addProps increment hinterpIncrement
    obtain rfl := (add_iff _ _ _ _ _).mp hinterpIncrement
    rintro ⟨zeroValue⟩ zero hZero hinterpZero
    cases zeroValue with
    | float _ | dense _ | string _ => simp at hZero
    | integer zeroAttr =>
      have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
      obtain rfl := (constant_iff _ zeroAttr _).mp hinterpZero
      rintro negProps source hinterpSource
      obtain rfl := (sub_iff _ _ _ _ _).mp hinterpSource
      rw [hOneValue, hZeroValue]
      simp only [IsTypeAttr.cast?_of]
      refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int w (.val z))
          (ofInt_normalizeValue { bitwidth := w, signedness := signedness } (-1)).symm
      refine ⟨.int w (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))), ?_, ?_⟩
      · exact (xor_iff _ _ _ _).mpr rfl
      change ∃ h : w = w,
        (LLVM.Int.sub (.val (BitVec.ofInt w 0))
          (LLVM.Int.add x (.val (BitVec.ofInt w 1)) addProps.nsw addProps.nuw)
          negProps.nsw negProps.nuw).cast h ⊒
          LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (neg_increment_refines w x addProps.nsw addProps.nuw negProps.nsw negProps.nuw)

/-- Commuted operand form selected by Negator's canonical operand ordering. -/
public def negateIncrementCommuted : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let one ← matchIntConstant ty 1
      let increment ← MatchProg.operation (.llvm .add) #[one, x] #[ty] (fun _ => true)
      let zero ← matchIntConstant ty 0
      let _ ← MatchProg.root (.llvm .sub) #[zero, increment.res[0]!] #[ty] (fun _ => true)
      return (ty, x))
    (fun (ty, x) => do
      let minusOneProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty fun type => do
          let some intType := type.cast? IntegerType | none
          return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-1) intType))
      let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] minusOneProps
      let xorProps ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[x, minusOne.res[0]!] #[ty] xorProps)
    (fun result => result.res[0]!)

public theorem negateIncrementCommuted_valid : Pattern.Valid negateIncrementCommuted := by
  simp only [negateIncrementCommuted, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x
  rintro ⟨ov⟩ one hone hio
  cases ov with
  | float _ | dense _ | string _ => simp at hone
  | integer oa =>
    have ho : oa.value = 1 := of_decide_eq_true hone
    obtain rfl := (constant_iff _ oa _).mp hio
    rintro ap inc hi
    obtain rfl := (add_iff _ _ _ _ _).mp hi
    rintro ⟨zv⟩ zero hzero hiz
    cases zv with
    | float _ | dense _ | string _ => simp at hzero
    | integer za =>
      have hz : za.value = 0 := of_decide_eq_true hzero
      obtain rfl := (constant_iff _ za _).mp hiz
      rintro np source his
      obtain rfl := (sub_iff _ _ _ _ _).mp his
      rw [ho, hz]
      simp only [IsTypeAttr.cast?_of]
      refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int w (.val z))
          (ofInt_normalizeValue { bitwidth := w, signedness := s } (-1)).symm
      refine ⟨.int w (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      change ∃ h : w=w, (LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.add (.val (BitVec.ofInt w 1)) x ap.nsw ap.nuw) np.nsw np.nuw).cast h ⊒
        LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))
      exact ⟨rfl, by simpa only [LLVM.Int.cast_self] using
        neg_increment_commuted_refines w x ap.nsw ap.nuw np.nsw np.nuw⟩

end Veir.Passes.InstCombineLLVM.NegateIncrement
