import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
import Veir.PatternRewriter.Puddle.Validity
import Veir.Parser.MlirParser
import Veir.Printer

open Veir
open Veir.Puddle
open Veir.Parser
open Veir.Data

/-!
## Useful lemmas for reasoning about `InterpretsTo` and `RuntimeValue` refinements
-/

private theorem constant_iff (ty : IntegerType) (props : propertiesOf (.arith .constant : OpCode))
    (v : RuntimeValue) :
    InterpretsTo (.arith .constant) props #[ty] #[] #[v] ↔
      v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth props.value.value)) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms, List.getElem!_toArray,
    List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero,
    Option.getD_some, true_and, interpretOp', Arith.interpretOp', List.getElem_toArray,
    Attribute.asType_val, Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

private theorem addi_iff (w : Nat) (props : propertiesOf (.arith .addi : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .addi) props #[IntegerType.mk w] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.add x y props.attr.nsw props.attr.nuw) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms, List.getElem!_toArray,
    List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero,
    Option.getD_some, true_and, interpretOp', Arith.interpretOp', ne_eq, not_true_eq_false,
    ↓reduceDIte, LLVM.Int.cast_self, Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

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

private theorem add_zero_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.add x (.val (BitVec.ofInt w 0)) nsw nuw) ⊒ .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure]
  grind

private theorem mul_two_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (BitVec.ofInt w 2)) nsw nuw) ⊒
      .int w (LLVM.Int.add x x) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.mul, LLVM.Int.add,
    isRefinedBy, Id.run, pure, BitVec.mul_two]
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
  simp only [TypeAttr.of, Coe.coe, Attribute.asType, RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val propzero hinterpCst
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro addProp val hinterpAdd
  obtain rfl := (addi_iff _ _ _ _ _).mp hinterpAdd
  grind [add_zero_refines]

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
  simp only [TypeAttr.of, Coe.coe, Attribute.asType, RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val proptwo hinterpCst
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro mulProp val hinterpMul
  obtain rfl := (muli_iff _ _ _ _ _).mp hinterpMul
  exists (.int w (LLVM.Int.add x x))
  constructor; exact (addi_iff _ _ _ _ _).mpr rfl
  grind [mul_two_refines]

/-- Rewrite `x + 0` to `x`, matching the zero with a native metadata predicate. -/
private def nativeMatch : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cst ← MatchProg.operation (.arith .constant) #[] #[returnType]
      MatchProg.matchNative (returnType, cst.properties)
        (fun (type, properties) =>
          type = (IntegerType.signless 32) && properties.value.value = 0)
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
  simp only [TypeAttr.of, Coe.coe, Attribute.asType, RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val hinterpCst
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro addProp val hinterpAddi
  obtain rfl := (addi_iff _ _ _ _ _).mp hinterpAddi
  intro _
  obtain rfl : w = 32 := by grind
  intro cstPropZero
  grind [add_zero_refines]

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
