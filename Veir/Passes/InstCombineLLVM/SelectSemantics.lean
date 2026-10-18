module

public import Veir.Passes.InstCombineLLVM.CompareSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM

open Veir Veir.Data Veir.Puddle

public abbrev selectConstantProperty (value : Int) (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt value intType))

public abbrev matchSelectConstant (ty : Handle OpCode .type) (value : Int) :
    MatchProg.Builder (Handle OpCode .value) := do
  let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] fun properties =>
    match (asLLVMConstantProperties properties).value with
    | .integer attr => attr.value = value
    | _ => false
  return constant.res[0]!

public theorem select_iff {signedness : IntegerType.Signedness} (w : Nat)
    (c : LLVM.Int 1) (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .select) ()
      #[IntegerType.mk w signedness]
      #[.int 1 c, .int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.select c x y) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff,
    RuntimeValue.Conforms, List.getElem!_toArray, List.getElem!_eq_getElem?_getD,
    forall_eq, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero,
    Option.getD_some, true_and, interpretOp', Llvm.interpretOp', ne_eq,
    not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self, Interp.pure_eq,
    Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public abbrev i1zero : LLVM.Int 1 := .val (BitVec.ofInt 1 0)
public abbrev i1one : LLVM.Int 1 := .val (BitVec.ofInt 1 1)
public abbrev i1not (x : LLVM.Int 1) : LLVM.Int 1 := LLVM.Int.xor x i1one
public abbrev logicalAnd (x y : LLVM.Int 1) : LLVM.Int 1 := LLVM.Int.select x y i1zero
public abbrev logicalOr (x y : LLVM.Int 1) : LLVM.Int 1 := LLVM.Int.select x i1one y

private theorem i1_cases (x : BitVec 1) : x = 0 ∨ x = 1 :=
  BitVec.eq_zero_or_eq_one x

private theorem llvm_i1_cases (x : LLVM.Int 1) :
    x = .poison ∨ x = i1zero ∨ x = i1one := by
  cases x with
  | poison => exact Or.inl rfl
  | val x =>
    rcases i1_cases x with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

public theorem select_false_invert (a b : LLVM.Int 1) :
    LLVM.Int.select a i1zero b = LLVM.Int.select (i1not a) b i1zero := by
  cases a with
  | poison => simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
  | val a =>
    rcases i1_cases a with rfl | rfl <;>
      simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]

public theorem select_true_invert (a b : LLVM.Int 1) :
    LLVM.Int.select a b i1one = LLVM.Int.select (i1not a) i1one b := by
  cases a with
  | poison => simp [i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
  | val a =>
    rcases i1_cases a with rfl | rfl <;>
      simp [i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]

public theorem select_nested_true (a b : LLVM.Int 1) :
    LLVM.Int.select (LLVM.Int.select a i1one b) i1one b =
      LLVM.Int.select a i1one b := by
  cases a with
  | poison => simp [i1one, LLVM.Int.select, Id.run]
  | val a =>
    rcases i1_cases a with rfl | rfl
    all_goals
      cases b with
      | poison => simp [i1one, LLVM.Int.select, Id.run]
      | val b =>
        rcases i1_cases b with rfl | rfl <;>
          simp [i1one, LLVM.Int.select, Id.run]

public theorem select_nested_false (a b : LLVM.Int 1) :
    LLVM.Int.select (LLVM.Int.select a b i1zero) b i1zero =
      LLVM.Int.select a b i1zero := by
  cases a with
  | poison => simp [i1zero, LLVM.Int.select, Id.run]
  | val a =>
    rcases i1_cases a with rfl | rfl
    all_goals
      cases b with
      | poison => simp [i1zero, LLVM.Int.select, Id.run]
      | val b =>
        rcases i1_cases b with rfl | rfl <;>
          simp [i1zero, LLVM.Int.select, Id.run]

public theorem select_demorgan_and (a b : LLVM.Int 1) :
    LLVM.Int.select (i1not a) (i1not b) i1zero =
      i1not (LLVM.Int.select a i1one b) := by
  cases a with
  | poison => simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
  | val a =>
    rcases i1_cases a with rfl | rfl
    all_goals
      cases b with
      | poison => simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
      | val b =>
        rcases i1_cases b with rfl | rfl <;>
          simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]

public theorem select_demorgan_or (a b : LLVM.Int 1) :
    LLVM.Int.select (i1not a) i1one (i1not b) =
      i1not (LLVM.Int.select a b i1zero) := by
  cases a with
  | poison => simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
  | val a =>
    rcases i1_cases a with rfl | rfl
    all_goals
      cases b with
      | poison => simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
      | val b =>
        rcases i1_cases b with rfl | rfl <;>
          simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]

public theorem select_or_not_condition (a b c : LLVM.Int 1) (disjoint : Bool) :
    LLVM.Int.select (LLVM.Int.or (i1not a) c disjoint) a b ⊒
      LLVM.Int.select a (LLVM.Int.select c i1one b) i1zero := by
  cases a with
  | poison =>
    cases c <;> cases b <;>
      simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor,
        LLVM.Int.or, isRefinedBy, Id.run]
  | val a =>
    rcases i1_cases a with rfl | rfl
    all_goals
      cases c with
      | poison =>
        cases b <;> cases disjoint <;>
          simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor,
            LLVM.Int.or, isRefinedBy, Id.run]
      | val c =>
        rcases i1_cases c with rfl | rfl
        all_goals
          cases b <;> cases disjoint <;>
            simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor,
              LLVM.Int.or, isRefinedBy, Id.run]

public theorem select_and_not_condition (a b c : LLVM.Int 1) :
    LLVM.Int.select (LLVM.Int.and (i1not c) b) a b ⊒
      LLVM.Int.select b (LLVM.Int.select c i1one a) i1zero := by
  rcases llvm_i1_cases a with rfl | rfl | rfl <;>
    rcases llvm_i1_cases b with rfl | rfl | rfl <;>
    rcases llvm_i1_cases c with rfl | rfl | rfl <;>
    simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor,
      LLVM.Int.and, isRefinedBy, Id.run]

public theorem select_or_inverted_condition (a b c : LLVM.Int 1)
    (disjoint : Bool) :
    LLVM.Int.select (LLVM.Int.or a (i1not c) disjoint) a b ⊒
      LLVM.Int.select a i1one (LLVM.Int.select c b i1zero) := by
  rcases llvm_i1_cases a with rfl | rfl | rfl <;>
    rcases llvm_i1_cases b with rfl | rfl | rfl <;>
    rcases llvm_i1_cases c with rfl | rfl | rfl <;> cases disjoint <;>
    simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor,
      LLVM.Int.or, isRefinedBy, Id.run]

public theorem select_and_not_false (a b c : LLVM.Int 1) :
    LLVM.Int.select (LLVM.Int.and c (i1not b)) a b ⊒
      LLVM.Int.select b i1one (LLVM.Int.select c a i1zero) := by
  rcases llvm_i1_cases a with rfl | rfl | rfl <;>
    rcases llvm_i1_cases b with rfl | rfl | rfl <;>
    rcases llvm_i1_cases c with rfl | rfl | rfl <;>
    simp [i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor,
      LLVM.Int.and, isRefinedBy, Id.run]

public theorem select_demorgan_xor
    (andSelect orSelect notLeft outerSwapped orSwapped : Bool)
    (a b : LLVM.Int 1) (disjoint : Bool) :
    let innerAnd := if andSelect then logicalAnd a b else LLVM.Int.and a b
    let innerOr := if orSelect then
      (if orSwapped then logicalOr b a else logicalOr a b)
    else if orSwapped then LLVM.Int.or b a disjoint else LLVM.Int.or a b disjoint
    let notInner := if notLeft then LLVM.Int.xor i1one innerAnd else i1not innerAnd
    LLVM.Int.select (if outerSwapped then innerOr else notInner)
      (if outerSwapped then notInner else innerOr) i1zero ⊒
      LLVM.Int.xor a b := by
  rcases llvm_i1_cases a with rfl | rfl | rfl <;>
    rcases llvm_i1_cases b with rfl | rfl | rfl <;>
    cases andSelect <;> cases orSelect <;> cases notLeft <;> cases outerSwapped <;>
    cases orSwapped <;> cases disjoint <;>
    simp [logicalAnd, logicalOr, i1zero, i1one, i1not, LLVM.Int.select,
      LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, isRefinedBy, Id.run]

public theorem select_not_swap {w : Nat} (c : LLVM.Int 1) (x y : LLVM.Int w) :
    LLVM.Int.select (i1not c) x y = LLVM.Int.select c y x := by
  cases c with
  | poison => simp [i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
  | val c =>
    rcases i1_cases c with rfl | rfl <;>
      simp [i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]

public theorem select_symmetric {w : Nat} (c1 c2 : LLVM.Int 1)
    (a b : LLVM.Int w) :
    LLVM.Int.select c2 (LLVM.Int.select c1 a b) (LLVM.Int.select c1 b a) =
      LLVM.Int.select (LLVM.Int.xor c1 c2) b a := by
  cases c1 with
  | poison => cases c2 <;> simp [LLVM.Int.select, LLVM.Int.xor, Id.run]
  | val c1 =>
    rcases i1_cases c1 with rfl | rfl
    · cases c2 with
      | poison => simp [LLVM.Int.select, LLVM.Int.xor, Id.run]
      | val c2 =>
        rcases i1_cases c2 with rfl | rfl <;>
          simp [LLVM.Int.select, LLVM.Int.xor, Id.run]
    · cases c2 with
      | poison => simp [LLVM.Int.select, LLVM.Int.xor, Id.run]
      | val c2 =>
        rcases i1_cases c2 with rfl | rfl <;>
          simp [LLVM.Int.select, LLVM.Int.xor, Id.run]

public theorem select_nested_and {w : Nat} (c0 c1 : LLVM.Int 1)
    (a b : LLVM.Int w) :
    LLVM.Int.select c0 (LLVM.Int.select c1 a b) b =
      LLVM.Int.select (logicalAnd c0 c1) a b := by
  cases c0 with
  | poison => simp [logicalAnd, i1zero, LLVM.Int.select, Id.run]
  | val c0 =>
    rcases i1_cases c0 with rfl | rfl
    · simp [logicalAnd, i1zero, LLVM.Int.select, Id.run]
    · cases c1 with
      | poison => simp [logicalAnd, i1zero, LLVM.Int.select, Id.run]
      | val c1 =>
        rcases i1_cases c1 with rfl | rfl <;>
          simp [logicalAnd, i1zero, LLVM.Int.select, Id.run]

public theorem select_nested_and_not {w : Nat} (c0 c1 : LLVM.Int 1)
    (a b : LLVM.Int w) :
    LLVM.Int.select c0 (LLVM.Int.select c1 b a) b =
      LLVM.Int.select (logicalAnd c0 (i1not c1)) a b := by
  cases c0 with
  | poison => simp [logicalAnd, i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
  | val c0 =>
    rcases i1_cases c0 with rfl | rfl
    · simp [logicalAnd, i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
    · cases c1 with
      | poison => simp [logicalAnd, i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
      | val c1 =>
        rcases i1_cases c1 with rfl | rfl <;>
          simp [logicalAnd, i1zero, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]

public theorem select_nested_or {w : Nat} (c0 c1 : LLVM.Int 1)
    (a b : LLVM.Int w) :
    LLVM.Int.select c0 a (LLVM.Int.select c1 a b) =
      LLVM.Int.select (logicalOr c0 c1) a b := by
  cases c0 with
  | poison => simp [logicalOr, i1one, LLVM.Int.select, Id.run]
  | val c0 =>
    rcases i1_cases c0 with rfl | rfl
    · cases c1 with
      | poison => simp [logicalOr, i1one, LLVM.Int.select, Id.run]
      | val c1 =>
        rcases i1_cases c1 with rfl | rfl <;>
          simp [logicalOr, i1one, LLVM.Int.select, Id.run]
    · simp [logicalOr, i1one, LLVM.Int.select, Id.run]

public theorem select_nested_or_not {w : Nat} (c0 c1 : LLVM.Int 1)
    (a b : LLVM.Int w) :
    LLVM.Int.select c0 a (LLVM.Int.select c1 b a) =
      LLVM.Int.select (logicalOr c0 (i1not c1)) a b := by
  cases c0 with
  | poison => simp [logicalOr, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
  | val c0 =>
    rcases i1_cases c0 with rfl | rfl
    · cases c1 with
      | poison => simp [logicalOr, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
      | val c1 =>
        rcases i1_cases c1 with rfl | rfl <;>
          simp [logicalOr, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]
    · simp [logicalOr, i1one, i1not, LLVM.Int.select, LLVM.Int.xor, Id.run]

/-- Shared executable template for the source's two condition-inverting boolean selects.
    `false` is `select(A, false, B)` and `true` is `select(A, B, true)`. -/
public def selectInvertPattern (falseArmIsOne : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let armConstant ← matchSelectConstant ty (if falseArmIsOne then 1 else 0)
    let _ ← MatchProg.root (.llvm .select)
      (if falseArmIsOne then #[a, b, armConstant] else #[a, armConstant, b])
      #[ty]
    return (ty, a, b, armConstant))
  (fun (ty, a, b, armConstant) => do
    let one ← if falseArmIsOne then pure armConstant else do
      let cp ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        ty (selectConstantProperty 1)
      let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] cp
      pure c.res[0]!
    let xp ← CreateProg.property (.llvm .xor) ()
    let notA ← CreateProg.operation (.llvm .xor) #[a, one] #[ty] xp
    let sp ← CreateProg.property (.llvm .select) ()
    CreateProg.operation (.llvm .select)
      (if falseArmIsOne then #[notA.res[0]!, armConstant, b]
        else #[notA.res[0]!, b, armConstant]) #[ty] sp)
  (fun result => result.res[0]!)

public theorem selectInvertPattern_valid (falseArmIsOne : Bool) :
    Pattern.Valid (selectInvertPattern falseArmIsOne) := by
  cases falseArmIsOne
  · simp only [selectInvertPattern, Bool.false_eq_true, ite_false,
      matchSelectConstant]
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro type ⟨w, signedness⟩ hType hWidth
    subst type
    change w = 1 at hWidth
    subst w
    rintro a hA b hB
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro property armConstant hConstant hArmConstant
    let property' : LLVMConstantProperties := asLLVMConstantProperties property
    change (match property'.value with
        | .integer attr => decide (attr.value = 0)
        | _ => false) = true at hConstant
    change InterpretsTo (.llvm .mlir__constant) property'
      #[IntegerType.mk 1 signedness] #[] #[armConstant] at hArmConstant
    rcases property' with ⟨constantValue⟩
    cases constantValue with
    | float _ | dense _ | string _ => simp at hConstant
    | integer attr =>
      simp at hConstant
      obtain rfl := (constant_iff _ attr _).mp hArmConstant
      rintro ⟨⟩ source hSource
      obtain rfl := (select_iff _ _ _ _ _).mp hSource
      simp [selectConstantProperty, IsTypeAttr.cast?_of]
      refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int 1 (.val z))
          (ofInt_normalizeValue
            ({ bitwidth := 1, signedness := signedness } : IntegerType) 1).symm
      refine ⟨.int 1 (LLVM.Int.xor a (.val (BitVec.ofInt 1 1))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int 1 (LLVM.Int.select
        (LLVM.Int.xor a (.val (BitVec.ofInt 1 1))) b
        (.val (BitVec.ofInt 1 attr.value))), (select_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      rw [hConstant]
      have hEq :
          LLVM.Int.select a (.val (BitVec.ofInt 1 0)) b =
            LLVM.Int.select (LLVM.Int.xor a (.val (BitVec.ofInt 1 1))) b
              (.val (BitVec.ofInt 1 0)) := by
        simpa only [i1zero, i1one, i1not] using select_false_invert a b
      rw [hEq]
      simp only [LLVM.Int.cast_self, isRefinedBy_refl]
  · simp only [selectInvertPattern, Bool.true_eq, ite_true, matchSelectConstant]
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro type ⟨w, signedness⟩ hType hWidth
    subst type
    change w = 1 at hWidth
    subst w
    rintro a hA b hB
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro property armConstant hConstant hArmConstant
    let property' : LLVMConstantProperties := asLLVMConstantProperties property
    change (match property'.value with
      | .integer attr => decide (attr.value = 1)
      | _ => false) = true at hConstant
    change InterpretsTo (.llvm .mlir__constant) property'
      #[IntegerType.mk 1 signedness] #[] #[armConstant] at hArmConstant
    rcases property' with ⟨constantValue⟩
    cases constantValue with
    | float _ | dense _ | string _ => simp at hConstant
    | integer attr =>
      simp at hConstant
      obtain rfl := (constant_iff _ attr _).mp hArmConstant
      rintro ⟨⟩ source hSource
      obtain rfl := (select_iff _ _ _ _ _).mp hSource
      refine ⟨.int 1 (LLVM.Int.xor a (.val (BitVec.ofInt 1 attr.value))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int 1 (LLVM.Int.select
        (LLVM.Int.xor a (.val (BitVec.ofInt 1 attr.value)))
        (.val (BitVec.ofInt 1 attr.value)) b), (select_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      rw [hConstant]
      have hEq :
          LLVM.Int.select a b (.val (BitVec.ofInt 1 1)) =
            LLVM.Int.select (LLVM.Int.xor a (.val (BitVec.ofInt 1 1)))
              (.val (BitVec.ofInt 1 1)) b := by
        simpa only [i1one, i1not] using select_true_invert a b
      rw [hEq]
      simp only [LLVM.Int.cast_self, isRefinedBy_refl]

/-- Shared executable template for the two nested boolean-select identities.
    `true` selects the one-arm identity and `false` selects the zero-arm identity. -/
public def selectNestedPattern (oneArm : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let constant ← matchSelectConstant ty (if oneArm then 1 else 0)
    let inner ← MatchProg.operation (.llvm .select)
      (if oneArm then #[a, constant, b] else #[a, b, constant]) #[ty]
      (fun _ => true)
    let _ ← MatchProg.root (.llvm .select)
      (if oneArm then #[inner.res[0]!, constant, b]
        else #[inner.res[0]!, b, constant]) #[ty] (fun _ => true)
    return inner)
  (fun inner => pure inner)
  (fun result => result.res[0]!)

public theorem selectNestedPattern_valid (oneArm : Bool) :
    Pattern.Valid (selectNestedPattern oneArm) := by
  cases oneArm
  · simp only [selectNestedPattern, Bool.false_eq_true, ite_false,
      matchSelectConstant]
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro type ⟨w, signedness⟩ hType hWidth
    subst type
    change w = 1 at hWidth
    subst w
    rintro a hA b hB
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro property constant hConstant hConstantInterp
    let property' : LLVMConstantProperties := asLLVMConstantProperties property
    change (match property'.value with
      | .integer attr => decide (attr.value = 0)
      | _ => false) = true at hConstant
    change InterpretsTo (.llvm .mlir__constant) property'
      #[IntegerType.mk 1 signedness] #[] #[constant] at hConstantInterp
    rcases property' with ⟨constantValue⟩
    cases constantValue with
    | float _ | dense _ | string _ => simp at hConstant
    | integer attr =>
      simp at hConstant
      obtain rfl := (constant_iff _ attr _).mp hConstantInterp
      rintro ⟨⟩ inner hInner
      obtain rfl := (select_iff _ _ _ _ _).mp hInner
      rintro ⟨⟩ source hSource
      obtain rfl := (select_iff _ _ _ _ _).mp hSource
      refine ⟨rfl, ?_⟩
      rw [hConstant]
      have hEq := select_nested_false a b
      simp only [i1zero] at hEq
      rw [hEq]
      simp only [LLVM.Int.cast_self, isRefinedBy_refl]
  · simp only [selectNestedPattern, Bool.true_eq, ite_true, matchSelectConstant]
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro type ⟨w, signedness⟩ hType hWidth
    subst type
    change w = 1 at hWidth
    subst w
    rintro a hA b hB
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro property constant hConstant hConstantInterp
    let property' : LLVMConstantProperties := asLLVMConstantProperties property
    change (match property'.value with
      | .integer attr => decide (attr.value = 1)
      | _ => false) = true at hConstant
    change InterpretsTo (.llvm .mlir__constant) property'
      #[IntegerType.mk 1 signedness] #[] #[constant] at hConstantInterp
    rcases property' with ⟨constantValue⟩
    cases constantValue with
    | float _ | dense _ | string _ => simp at hConstant
    | integer attr =>
      simp at hConstant
      obtain rfl := (constant_iff _ attr _).mp hConstantInterp
      rintro ⟨⟩ inner hInner
      obtain rfl := (select_iff _ _ _ _ _).mp hInner
      rintro ⟨⟩ source hSource
      obtain rfl := (select_iff _ _ _ _ _).mp hSource
      refine ⟨rfl, ?_⟩
      rw [hConstant]
      have hEq := select_nested_true a b
      simp only [i1one] at hEq
      rw [hEq]
      simp only [LLVM.Int.cast_self, isRefinedBy_refl]

/-- Shared executable template for the direct nested-select logical AND/OR folds.
    `true` builds short-circuit logical AND; `false` builds logical OR. -/
public def selectNestedLogicalPattern (isAnd : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let valueTy ← MatchProg.type (Attr := IntegerType)
    let c0 ← MatchProg.value condTy
    let c1 ← MatchProg.value condTy
    let a ← MatchProg.value valueTy
    let b ← MatchProg.value valueTy
    let inner ← MatchProg.operation (.llvm .select) #[c1, a, b] #[valueTy]
      (fun _ => true)
    let root ← MatchProg.root (.llvm .select)
      (if isAnd then #[c0, inner.res[0]!, b] else #[c0, a, inner.res[0]!])
      #[valueTy] (fun _ => true)
    let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
      let operands := op.getOperands! ctx
      guard (operands.size = 3)
      let innerValue := operands[(if isAnd then 1 else 2)]!
      let some firstUse := innerValue.getFirstUse! ctx | none
      guard ((firstUse.getNextUse! ctx).isNone))
    return (condTy, valueTy, c0, c1, a, b))
  (fun (condTy, valueTy, c0, c1, a, b) => do
    let constantProperties ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      condTy (selectConstantProperty (if isAnd then 0 else 1))
    let constant ← CreateProg.operation (.llvm .mlir__constant) #[] #[condTy]
      constantProperties
    let logicalProperties ← CreateProg.property (.llvm .select) ()
    let logical ← CreateProg.operation (.llvm .select)
      (if isAnd then #[c0, c1, constant.res[0]!]
        else #[c0, constant.res[0]!, c1]) #[condTy] logicalProperties
    let selectProperties ← CreateProg.property (.llvm .select) ()
    CreateProg.operation (.llvm .select) #[logical.res[0]!, a, b]
      #[valueTy] selectProperties)
  (fun result => result.res[0]!)

public theorem selectNestedLogicalPattern_valid (isAnd : Bool) :
    Pattern.Valid (selectNestedLogicalPattern isAnd) := by
  cases isAnd
  · simp only [selectNestedLogicalPattern, Bool.false_eq_true, ite_false]
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro condType ⟨condW, condSignedness⟩ hCondType hCondWidth
    subst condType
    change condW = 1 at hCondWidth
    subst condW
    rintro ⟨valueW, valueSignedness⟩
    rintro c0 hC0 c1 hC1 a hA b hB
    obtain ⟨c0, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC0
    obtain ⟨c1, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC1
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro ⟨⟩ inner hInner
    obtain rfl := (select_iff _ _ _ _ _).mp hInner
    rintro ⟨⟩ source hSource
    obtain rfl := (select_iff _ _ _ _ _).mp hSource
    rintro ⟨⟩
    simp [selectConstantProperty, IsTypeAttr.cast?_of]
    refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int 1 (.val z))
        (ofInt_normalizeValue
          ({ bitwidth := 1, signedness := condSignedness } : IntegerType) 1).symm
    refine ⟨.int 1 (LLVM.Int.select c0 (.val (BitVec.ofInt 1 1)) c1),
      (select_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int valueW
      (LLVM.Int.select (LLVM.Int.select c0 (.val (BitVec.ofInt 1 1)) c1) a b),
      (select_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    have hEq := select_nested_or c0 c1 a b
    simp only [logicalOr, i1one] at hEq
    rw [hEq]
    simp only [LLVM.Int.cast_self, isRefinedBy_refl]
  · simp only [selectNestedLogicalPattern, Bool.true_eq, ite_true]
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro condType ⟨condW, condSignedness⟩ hCondType hCondWidth
    subst condType
    change condW = 1 at hCondWidth
    subst condW
    rintro ⟨valueW, valueSignedness⟩
    rintro c0 hC0 c1 hC1 a hA b hB
    obtain ⟨c0, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC0
    obtain ⟨c1, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC1
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro ⟨⟩ inner hInner
    obtain rfl := (select_iff _ _ _ _ _).mp hInner
    rintro ⟨⟩ source hSource
    obtain rfl := (select_iff _ _ _ _ _).mp hSource
    rintro ⟨⟩
    simp [selectConstantProperty, IsTypeAttr.cast?_of]
    refine ⟨.int 1 (.val (BitVec.ofInt 1 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int 1 (.val z))
        (ofInt_normalizeValue
          ({ bitwidth := 1, signedness := condSignedness } : IntegerType) 0).symm
    refine ⟨.int 1 (LLVM.Int.select c0 c1 (.val (BitVec.ofInt 1 0))),
      (select_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int valueW
      (LLVM.Int.select (LLVM.Int.select c0 c1 (.val (BitVec.ofInt 1 0))) a b),
      (select_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    have hEq := select_nested_and c0 c1 a b
    simp only [logicalAnd, i1zero] at hEq
    rw [hEq]
    simp only [LLVM.Int.cast_self, isRefinedBy_refl]

/-- Shared executable template for the nested-select folds whose generated
    short-circuit condition contains `not C1`. `true` selects AND, `false` OR. -/
public def selectNestedLogicalNotPattern (isAnd : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let valueTy ← MatchProg.type (Attr := IntegerType)
    let c0 ← MatchProg.value condTy
    let c1 ← MatchProg.value condTy
    let a ← MatchProg.value valueTy
    let b ← MatchProg.value valueTy
    let inner ← MatchProg.operation (.llvm .select) #[c1, b, a] #[valueTy]
      (fun _ => true)
    let root ← MatchProg.root (.llvm .select)
      (if isAnd then #[c0, inner.res[0]!, b] else #[c0, a, inner.res[0]!])
      #[valueTy] (fun _ => true)
    let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
      let operands := op.getOperands! ctx
      guard (operands.size = 3)
      let innerValue := operands[(if isAnd then 1 else 2)]!
      let some firstUse := innerValue.getFirstUse! ctx | none
      guard ((firstUse.getNextUse! ctx).isNone))
    return (condTy, valueTy, c0, c1, a, b))
  (fun (condTy, valueTy, c0, c1, a, b) => do
    let oneProperties ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      condTy (selectConstantProperty 1)
    let one ← CreateProg.operation (.llvm .mlir__constant) #[] #[condTy]
      oneProperties
    let xorProperties ← CreateProg.property (.llvm .xor) ()
    let notC1 ← CreateProg.operation (.llvm .xor) #[c1, one.res[0]!]
      #[condTy] xorProperties
    let logicalConstant ← if isAnd then do
      let zeroProperties ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        condTy (selectConstantProperty 0)
      CreateProg.operation (.llvm .mlir__constant) #[] #[condTy] zeroProperties
    else pure one
    let logicalProperties ← CreateProg.property (.llvm .select) ()
    let logical ← CreateProg.operation (.llvm .select)
      (if isAnd then #[c0, notC1.res[0]!, logicalConstant.res[0]!]
        else #[c0, logicalConstant.res[0]!, notC1.res[0]!])
      #[condTy] logicalProperties
    let selectProperties ← CreateProg.property (.llvm .select) ()
    CreateProg.operation (.llvm .select) #[logical.res[0]!, a, b]
      #[valueTy] selectProperties)
  (fun result => result.res[0]!)

public theorem selectNestedLogicalNotPattern_valid (isAnd : Bool) :
    Pattern.Valid (selectNestedLogicalNotPattern isAnd) := by
  cases isAnd
  · simp only [selectNestedLogicalNotPattern, Bool.false_eq_true, ite_false]
    unfoldPuddleBuilder
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro condType ⟨condW, condSignedness⟩ hCondType hCondWidth
    subst condType
    change condW = 1 at hCondWidth
    subst condW
    rintro ⟨valueW, valueSignedness⟩
    rintro c0 hC0 c1 hC1 a hA b hB
    obtain ⟨c0, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC0
    obtain ⟨c1, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC1
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro ⟨⟩ inner hInner
    obtain rfl := (select_iff _ _ _ _ _).mp hInner
    rintro ⟨⟩ source hSource
    obtain rfl := (select_iff _ _ _ _ _).mp hSource
    rintro ⟨⟩
    simp [selectConstantProperty, IsTypeAttr.cast?_of]
    refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int 1 (.val z))
        (ofInt_normalizeValue
          ({ bitwidth := 1, signedness := condSignedness } : IntegerType) 1).symm
    refine ⟨.int 1 (LLVM.Int.xor c1 (.val (BitVec.ofInt 1 1))),
      (xor_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int 1 (LLVM.Int.select c0 (.val (BitVec.ofInt 1 1))
      (LLVM.Int.xor c1 (.val (BitVec.ofInt 1 1)))),
      (select_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int valueW (LLVM.Int.select
      (LLVM.Int.select c0 (.val (BitVec.ofInt 1 1))
        (LLVM.Int.xor c1 (.val (BitVec.ofInt 1 1)))) a b),
      (select_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    have hEq := select_nested_or_not c0 c1 a b
    simp only [logicalOr, i1one, i1not] at hEq
    rw [hEq]
    simp only [LLVM.Int.cast_self, isRefinedBy_refl]
  · simp only [selectNestedLogicalNotPattern, Bool.true_eq, ite_true]
    unfoldPuddleBuilder
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of,
        ProofTactics.guard_eq_cond_punit,
        MatchProg.collectBindings, MatchProg.collectDeclBindings,
        MatchProg.rootResults?, HandleContext.forbid, HandleContext.forbidMany,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    rintro condType ⟨condW, condSignedness⟩ hCondType hCondWidth
    subst condType
    change condW = 1 at hCondWidth
    subst condW
    rintro ⟨valueW, valueSignedness⟩
    rintro c0 hC0 c1 hC1 a hA b hB
    obtain ⟨c0, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC0
    obtain ⟨c1, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC1
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro ⟨⟩ inner hInner
    obtain rfl := (select_iff _ _ _ _ _).mp hInner
    rintro ⟨⟩ source hSource
    obtain rfl := (select_iff _ _ _ _ _).mp hSource
    rintro ⟨⟩
    simp [selectConstantProperty, IsTypeAttr.cast?_of]
    refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int 1 (.val z))
        (ofInt_normalizeValue
          ({ bitwidth := 1, signedness := condSignedness } : IntegerType) 1).symm
    refine ⟨.int 1 (LLVM.Int.xor c1 (.val (BitVec.ofInt 1 1))),
      (xor_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int 1 (.val (BitVec.ofInt 1 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int 1 (.val z))
        (ofInt_normalizeValue
          ({ bitwidth := 1, signedness := condSignedness } : IntegerType) 0).symm
    refine ⟨.int 1 (LLVM.Int.select c0
      (LLVM.Int.xor c1 (.val (BitVec.ofInt 1 1))) (.val (BitVec.ofInt 1 0))),
      (select_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int valueW (LLVM.Int.select
      (LLVM.Int.select c0 (LLVM.Int.xor c1 (.val (BitVec.ofInt 1 1)))
        (.val (BitVec.ofInt 1 0))) a b),
      (select_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    have hEq := select_nested_and_not c0 c1 a b
    simp only [logicalAnd, i1zero, i1one, i1not] at hEq
    rw [hEq]
    simp only [LLVM.Int.cast_self, isRefinedBy_refl]

end Veir.Passes.InstCombineLLVM
