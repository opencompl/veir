import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
import Veir.PatternRewriter.Puddle.Validity
import Veir.Parser.MlirParser
import Veir.Printer

open Veir
open Veir.Puddle
open Veir.Parser
open Veir.Data

private theorem constant_iff (w : Nat) (props : propertiesOf (.arith .constant : OpCode))
    (v : RuntimeValue) :
    InterpretsTo (.arith .constant) props #[IntegerType.mk w] #[] #[v] ↔
      v = .int w (.val (BitVec.ofInt w props.value.value)) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · rintro rfl
    simp [Attribute.asType]

private theorem integer_value {ty : TypeAttr} {x : RuntimeValue}
    (ht : ((ty.cast? IntegerType).map (fun _ => true)).getD false = true)
    (hx : x.Conforms ty) :
    ∃ w v, ty = (IntegerType.mk w : TypeAttr) ∧ x = .int w v := by
  cases hc : ty.cast? IntegerType with
  | none => simp [hc] at ht
  | some t =>
    have hty := (IsTypeAttr.cast?_eq_some_iff ty t).mp hc
    subst ty
    obtain ⟨v, rfl⟩ := RuntimeValue.Conforms.integerType hx
    exact ⟨t.bitwidth, v, rfl, rfl⟩

private theorem addi_iff (w : Nat) (props : propertiesOf (.arith .addi : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .addi) props #[IntegerType.mk w] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.add x y props.attr.nsw props.attr.nuw) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · rintro rfl
    simp [Attribute.asType]

private theorem add_zero_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.add x (.val (BitVec.ofInt w 0)) nsw nuw) ⊒ .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure]
  grind

private theorem muli_iff (w : Nat) (props : propertiesOf (.arith .muli : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .muli) props #[IntegerType.mk w] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.mul x y props.attr.nsw props.attr.nuw) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · rintro rfl
    simp [Attribute.asType]

private theorem mul_two_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (BitVec.ofInt w 2)) nsw nuw) ⊒
      .int w (LLVM.Int.add x x) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.mul, LLVM.Int.add,
    isRefinedBy, Id.run, pure, BitVec.mul_two]
  grind

private theorem mul_four_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (BitVec.ofInt w 4)) nsw nuw) ⊒
      .int w (LLVM.Int.add (LLVM.Int.add x x) (LLVM.Int.add x x)) := by
  have four : BitVec.ofNat w 4 = (2 : BitVec w) + 2 := by simpa using (BitVec.ofNat_add (n := w) 2 2)
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.mul, LLVM.Int.add,
    isRefinedBy, Id.run, pure, four, BitVec.mul_add, BitVec.mul_two]
  grind

/- ## Example patterns -/

/-- Match an arithmetic constant of a given value. -/
def matchConstant (returnType : Handle OpCode .type) (constant : Int)
    : MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.arith .constant) #[] #[returnType]
    (fun properties => properties.value.value = constant)
  return op.res[0]!

/-- Rewrite `x + 0` to `x`. -/
private def addZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 0
      let _ ← MatchProg.root (.arith .addi) #[x, cstVal] #[returnType]
      return x)
    pure
    (fun x => x)

theorem addZero_valid : Pattern.Valid addZero := by
  simp only [addZero, matchConstant]
  provePuddleValid
  rintro ty ht value hx pc zero hc hz pp result hr
  obtain ⟨w, x, rfl, rfl⟩ := integer_value ht hx
  have hz' := (constant_iff w pc zero).mp hz
  rw [hc] at hz'
  subst zero
  have hr' := (addi_iff w pp x (.val (BitVec.ofInt w 0)) result).mp hr
  subst result
  exact add_zero_refines w x pp.attr.nsw pp.attr.nuw

/-- Rewrite `x * 2` to `x + x`. -/
private def mulTwo : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 2
      let _ ← MatchProg.root (.arith .muli) #[x, cstVal] #[returnType]
      return (returnType, x))
    (fun (returnType, x) => do
      let properties ← CreateProg.property (.arith .addi)
        (default : propertiesOf (.arith .addi : OpCode))
      let add ← CreateProg.operation (.arith .addi) #[x, x] #[returnType] properties
      return add)
    (fun result => result)

theorem mulTwo_valid : Pattern.Valid mulTwo := by
  simp only [mulTwo, matchConstant]
  provePuddleValid
  rintro ty ht value hx pc two hc hcst pp result hr
  obtain ⟨w, x, rfl, rfl⟩ := integer_value ht hx
  have hcst' := (constant_iff w pc two).mp hcst
  rw [hc] at hcst'
  subst two
  have hr' := (muli_iff w pp x (.val (BitVec.ofInt w 2)) result).mp hr
  subst result
  refine ⟨.int w (LLVM.Int.add x x), (addi_iff w default x x _).mpr rfl, ?_⟩
  exact mul_two_refines w x pp.attr.nsw pp.attr.nuw

/-- Rewrite `x * 4` to `(x + x) + (x + x)`, creating two operations. -/
private def mulFour : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 4
      let _ ← MatchProg.root (.arith .muli) #[x, cstVal] #[returnType]
      return (returnType, x))
    (fun (returnType, x) => do
      let properties ← CreateProg.property (.arith .addi)
        (default : propertiesOf (.arith .addi : OpCode))
      let doubled ← CreateProg.operation (.arith .addi) #[x, x] #[returnType] properties
      let quadrupled ← CreateProg.operation (.arith .addi)
        #[doubled.res[0]!, doubled.res[0]!] #[returnType] properties
      return quadrupled)
    (fun result => result)

theorem mulFour_valid : Pattern.Valid mulFour := by
  simp only [mulFour, matchConstant]
  provePuddleValid
  rintro ty ht value hx pc four hc hcst pp result hr
  obtain ⟨w, x, rfl, rfl⟩ := integer_value ht hx
  have hcst' := (constant_iff w pc four).mp hcst
  rw [hc] at hcst'
  subst four
  have hr' := (muli_iff w pp x (.val (BitVec.ofInt w 4)) result).mp hr
  subst result
  refine ⟨.int w (LLVM.Int.add x x), (addi_iff w default x x _).mpr rfl,
    .int w (LLVM.Int.add (LLVM.Int.add x x) (LLVM.Int.add x x)),
    (addi_iff w default _ _ _).mpr rfl, ?_⟩
  exact mul_four_refines w x pp.attr.nsw pp.attr.nuw

/-- Rewrite `x + 0` to `x`, matching the zero with a native metadata predicate. -/
private def nativeMatch : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cst ← MatchProg.operation (.arith .constant) #[] #[returnType]
      MatchProg.matchNative (returnType, cst.properties)
        (fun (type, properties) =>
          type = IntegerType.mk 32 && properties.value.value = 0)
      let _ ← MatchProg.root (.arith .addi) #[x, cst.res[0]!] #[returnType]
      return x)
    pure
    (fun x => x)

/-- Rewrite `x * 2` to `x + 3`, creating the constant metadata with a native function. -/
private def nativeApply : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cst ← MatchProg.operation (.arith .constant) #[] #[returnType]
        (fun properties => properties.value.value = 2)
      let _ ← MatchProg.root (.arith .muli) #[x, cst.res[0]!] #[returnType]
      return (returnType, x, cst.properties))
    (fun (returnType, x, properties) => do
      let (newType, newProperties) ← CreateProg.applyNative (returnType, properties)
        (fun (type, properties) =>
          some (type, { properties with
            value := { properties.value with value := properties.value.value + 1 } }))
      let constant ← CreateProg.operation (.arith .constant) #[] #[newType] newProperties
      let addProperties ← CreateProg.property (.arith .addi) default
      let add ← CreateProg.operation (.arith .addi) #[x, constant.res[0]!] #[newType] addProperties
      return add)
    (fun result => result)

theorem nativeMatch_valid : Pattern.Valid nativeMatch := by
  simp only [nativeMatch]
  provePuddleValid
  rintro ty ht value hx pc zero hz pp result hr _ hc
  obtain ⟨w, x, rfl, rfl⟩ := integer_value ht hx
  have hz' := (constant_iff w pc zero).mp hz
  rw [hc] at hz'
  subst zero
  have hr' := (addi_iff w pp x (.val (BitVec.ofInt w 0)) result).mp hr
  subst result
  exact add_zero_refines w x pp.attr.nsw pp.attr.nuw

/-- A native guard authored after the root can inspect its properties. -/
private def nativeRootGuard (expectNsw : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let zero ← matchConstant ty 0
      let root ← MatchProg.root (.arith .addi) #[x, zero] #[ty]
      MatchProg.matchNative root.properties (fun properties => properties.attr.nsw == expectNsw)
      return x)
    pure
    (fun x => x)

example : (nativeRootGuard false).StructurallyWellFormed := by native_decide

example : (nativeRootGuard false).matcher.ConstrainsRoot := by cbv

/-- Recreate a multiplication, copying its type and both properties through a native tuple. -/
private def nativeCopy : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let cst ← MatchProg.operation (.arith .constant) #[] #[ty]
      let root ← MatchProg.root (.arith .muli) #[x, cst.res[0]!] #[ty]
      return (ty, x, cst.properties, root.properties))
    (fun (ty, x, pc, pr) => do
      let (ty, pc, pr) ← CreateProg.applyNative (ty, pc, pr) some
      let cst ← CreateProg.operation (.arith .constant) #[] #[ty] pc
      CreateProg.operation (.arith .muli) #[x, cst.res[0]!] #[ty] pr)
    (fun result => result)

theorem nativeCopy_valid : nativeCopy.Valid := by
  simp only [nativeCopy]
  provePuddleValid
  -- Check the goal shape: no assignment, tuple resolution, or memory plumbing remains.
  guard_target = ∀ (ty : TypeAttr),
    ((ty.cast? IntegerType).map (fun _ => true)).getD false = true →
    ∀ (x : RuntimeValue), x.Conforms ty →
    ∀ (pc : propertiesOf (.arith .constant : OpCode)) (cst : RuntimeValue),
    InterpretsTo (.arith .constant) pc #[ty] #[] #[cst] →
    ∀ (pr : propertiesOf (.arith .muli : OpCode)) (result : RuntimeValue),
    InterpretsTo (.arith .muli) pr #[ty] #[x, cst] #[result] →
    ∃ cst', InterpretsTo (.arith .constant) pc #[ty] #[] #[cst'] ∧
      ∃ result', InterpretsTo (.arith .muli) pr #[ty] #[x, cst'] #[result'] ∧ result ⊒ result'
  intro ty _ x _ pc cst hc pr result hr
  exact ⟨cst, hc, result, hr, RuntimeValue.isRefinedBy_refl result⟩

/-- The execution-only native example is deliberately not semantics-preserving. -/
theorem nativeApply_not_valid : ¬ nativeApply.Valid := by
  suffices ¬ nativeApply.PreservesSemantics from fun h => this h.refines
  unfold nativeApply
  unfoldPuddleBuilder
  simpPuddleSemantics
  refine ⟨IntegerType.mk 32, by decide, .int 32 (.val 42), by decide,
    { value := ⟨2, ⟨32⟩⟩ }, rfl, .int 32 (.val 2), ?_,
    default, .int 32 (.val 84), ?_, ?_⟩
  · exact (constant_iff 32 _ _).mpr rfl
  · exact (muli_iff 32 default (.val 42) (.val 2) _).mpr rfl
  · intro three hc result hr
    have hc' := (constant_iff 32 _ _).mp hc
    change three = .int 32 (.val 3) at hc'
    subst three
    have hr' := (addi_iff 32 default (.val 42) (.val 3) _).mp hr
    change result = .int 32 (.val 45) at hr'
    subst result
    simp [RuntimeValue.isRefinedBy, isRefinedBy]

/-- The interpreter computes the right sum, but the new result annotation is wrong. -/
private def badResultType : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let root ← MatchProg.root (.arith .addi) #[x, y] #[ty]
      return (x, y, root.properties))
    (fun (x, y, props) => do
      let ty ← CreateProg.type (IntegerType.mk 64)
      CreateProg.operation (.arith .addi) #[x, y] #[ty] props)
    (fun result => result)

example : badResultType.StructurallyWellFormed := by native_decide

theorem badResultType_not_valid : ¬ badResultType.Valid := by
  suffices ¬ badResultType.PreservesSemantics from fun h => this h.refines
  unfold badResultType
  unfoldPuddleBuilder
  simpPuddleSemantics
  refine ⟨IntegerType.mk 32, by decide, .int 32 (.val 1), by decide,
    .int 32 (.val 2), by decide, default, .int 32 (.val 3), ?_, ?_⟩
  · exact (addi_iff 32 default (.val 1) (.val 2) _).mpr rfl
  · intro result hr
    have hi := hr.2 .empty
    have ht := hr.1
    change Interp.ok (#[.int 32 (.val 3)], MemoryState.empty, none) =
      .ok (#[result], MemoryState.empty, none) at hi
    have heq : result = .int 32 (.val 3) := by simpa using hi.symm
    subst result
    have impossible : (64 : Nat) = 32 := ht.2 0 (by decide)
    contradiction

/-- Copy both outputs of a real two-result operation. -/
private def copyTwoResults : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let flagTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let root ← MatchProg.root (.arith .addui_extended) #[x, y] #[ty, flagTy]
      return (ty, flagTy, x, y, root.properties))
    (fun (ty, flagTy, x, y, props) =>
      CreateProg.operation (.arith .addui_extended) #[x, y] #[ty, flagTy] props)
    (fun result => result)

theorem copyTwoResults_valid : copyTwoResults.Valid := by
  simp only [copyTwoResults]
  provePuddleValid
  guard_target = ∀ (ty : TypeAttr),
    ((ty.cast? IntegerType).map (fun _ => true)).getD false = true →
    ∀ (flagTy : TypeAttr),
    ((flagTy.cast? IntegerType).map (fun _ => true)).getD false = true →
    ∀ (x : RuntimeValue), x.Conforms ty →
    ∀ (y : RuntimeValue), y.Conforms ty →
    ∀ (props : propertiesOf (.arith .addui_extended : OpCode)) (sum overflow : RuntimeValue),
    InterpretsTo (.arith .addui_extended) props #[ty, flagTy] #[x, y] #[sum, overflow] →
    ∃ sum' overflow',
      InterpretsTo (.arith .addui_extended) props #[ty, flagTy] #[x, y] #[sum', overflow'] ∧
      sum ⊒ sum' ∧ overflow ⊒ overflow'
  intro ty _ flagTy _ x _ y _ props sum overflow h
  exact ⟨sum, overflow, h, RuntimeValue.isRefinedBy_refl sum,
    RuntimeValue.isRefinedBy_refl overflow⟩

/-- Creation cannot silently truncate two interpreted results to one handle. -/
example (assignment : SemanticAssignment) (opCode : OpCode)
    (operands : Array (Handle OpCode .value)) (types : Array (Handle OpCode .type))
    (prop : Handle OpCode (.prop opCode)) (op : Handle OpCode .op)
    (result : Handle OpCode .value) (values : List RuntimeValue) (resultTypes : List TypeAttr)
    (property : propertiesOf opCode) (first second : RuntimeValue)
    (hv : assignment.getValues operands.toList = some values)
    (ht : assignment.getTypes types.toList = some resultTypes)
    (hp : assignment.getProperty prop = some property)
    (hi : interpretOp' opCode property resultTypes.toArray values.toArray #[] .empty =
      .ok (#[first, second], .empty, none)) :
    ¬ CreateDecl.Models (.operation opCode operands types prop op #[result]) assignment
      (fun _ => True) := by
  simp [CreateDecl.Models, hv, ht, hp, SemanticAssignment.existsValues]
  intro value h
  have hresult := h.2 .empty
  simp [hi] at hresult

/- ## Test matcher builder validation -/

/-- A matcher that is missing a root declaration. -/
private def missingRootBuilder : MatchProg.Builder Unit := pure ()

#guard_panic in
#eval (MatchProg.build missingRootBuilder).rootHandle.id

/-- A matcher that has a duplicate root declaration. -/
private def duplicateRootBuilder : MatchProg.Builder Unit := do
  let _ ← MatchProg.root (.arith .addi) #[] #[]
  let _ ← MatchProg.root (.arith .addi) #[] #[]
  return ()

#guard_panic in
#eval (MatchProg.build duplicateRootBuilder).rootHandle.id

/- ## Test pattern execution -/

private structure BinaryProgram where
  ctx : WfIRContext OpCode
  moduleOp : OperationPtr

/-- Parse a complete test module. -/
private def parseBinaryProgram (source : String) : Option BinaryProgram := do
  let (ctx, _) ← WfIRContext.create OpCode
  let parser ← (ParserState.fromInput source.toByteArray).toOption
  let (moduleOp, state, _) ←
    (Veir.Parser.parseTopLevelOp.run (MlirParserState.fromContext ctx) parser).toOption
  return ⟨state.ctx, moduleOp⟩

private def addZeroProgram := r#""builtin.module"() ({
  %input = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  %zero = "arith.constant"() <{ value = 0 : i32 }> : () -> i32
  %root = "arith.addi"(%input, %zero) : (i32, i32) -> i32
  "test.test"(%root) : (i32) -> ()
}) : () -> ()"#

private def mulTwoProgram := r#""builtin.module"() ({
  %input = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  %two = "arith.constant"() <{ value = 2 : i32 }> : () -> i32
  %root = "arith.muli"(%input, %two) : (i32, i32) -> i32
  "test.test"(%root) : (i32) -> ()
}) : () -> ()"#

private def mulFourProgram := r#""builtin.module"() ({
  %input = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  %four = "arith.constant"() <{ value = 4 : i32 }> : () -> i32
  %root = "arith.muli"(%input, %four) : (i32, i32) -> i32
  "test.test"(%root) : (i32) -> ()
}) : () -> ()"#

/-- Parse a program, apply a compiled Puddle pattern, and print the resulting module. -/
private def rewriteAndPrint (source : String) (rule : Pattern OpCode) : IO Unit := do
  let some program := parseBinaryProgram source | IO.println "parse failed"
  let pattern := Pattern.compile rule
  let some ctx := RewritePattern.applyInContext pattern.run program.ctx | IO.println "rewrite failed"
  Printer.printModule ctx.raw program.moduleOp

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%5) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram addZero

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %10 = "arith.addi"(%5, %5) : (i32, i32) -> i32
    "test.test"(%10) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint mulTwoProgram mulTwo

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%5) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram nativeMatch

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%5) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram (nativeRootGuard false)

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %6 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %7 = "arith.addi"(%5, %6) : (i32, i32) -> i32
    "test.test"(%7) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram (nativeRootGuard true)

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %10 = "arith.constant"() <{"value" = 3 : i32}> : () -> i32
    %11 = "arith.addi"(%5, %10) : (i32, i32) -> i32
    "test.test"(%11) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint mulTwoProgram nativeApply

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %10 = "arith.addi"(%5, %5) : (i32, i32) -> i32
    %11 = "arith.addi"(%10, %10) : (i32, i32) -> i32
    "test.test"(%11) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint mulFourProgram mulFour
