import Veir.PatternRewriter.Puddle
import Veir.Data.LLVM.Int.Lemmas
import Veir.Parser.MlirParser
import Veir.Printer

open Veir
open Veir.Puddle
open Veir.Parser

/- ## Example patterns -/

/-- Match an arithmetic constant of a given value. -/
def matchConstant (returnType : Handle OpCode .type) (constant : Int)
    : MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.arith .constant) #[] #[returnType]
    (fun properties => properties.value.value = constant)
  return op.res[0]!

@[simp]
private theorem llvmInt_add_val_zero {width : Nat} (value : Data.LLVM.Int width)
    (nsw nuw : Bool) :
    Data.LLVM.Int.add value (.val 0#width) nsw nuw = value := by
  simpa [Data.LLVM.Int.constant] using Data.LLVM.Int.add_zero value nsw nuw

@[simp]
private theorem llvmInt_sub_val_zero {width : Nat} (value : Data.LLVM.Int width)
    (nsw nuw : Bool) :
    Data.LLVM.Int.sub value (.val 0#width) nsw nuw = value := by
  simpa [Data.LLVM.Int.constant] using Data.LLVM.Int.sub_zero value nsw nuw

@[simp]
private theorem llvmInt_mul_val_one_refines {width : Nat} (value : Data.LLVM.Int width)
    (nsw nuw : Bool) :
    Data.LLVM.Int.mul value (.val 1#width) nsw nuw ⊒ value := by
  simpa [Data.LLVM.Int.constant] using Data.LLVM.Int.mul_one_refines value nsw nuw

@[simp]
private theorem llvmInt_mul_val_two {width : Nat} (value : Data.LLVM.Int width) :
    Data.LLVM.Int.mul value (.val 2#width) false false ⊒
      Data.LLVM.Int.add value value false false := by
  cases value <;>
    simp [Data.LLVM.Int.mul, Data.LLVM.Int.add, Id.run, isRefinedBy, BitVec.mul_two]

@[simp]
private theorem llvmInt_mul_val_zero_refines {width : Nat} (value : Data.LLVM.Int width)
    (nsw nuw : Bool) :
    Data.LLVM.Int.mul value (.val 0#width) nsw nuw ⊒ .val 0#width := by
  cases value with
  | poison => simp [Data.LLVM.Int.mul, Id.run, isRefinedBy]
  | val value =>
    simp only [Data.LLVM.Int.mul, Id.run]
    split
    · simp [pure, isRefinedBy]
    · split <;> simp [pure, isRefinedBy]

@[simp]
private theorem llvmInt_and_self {width : Nat} (value : Data.LLVM.Int width) :
    Data.LLVM.Int.and value value = value := by
  cases value <;> simp [Data.LLVM.Int.and, Id.run]

@[simp]
private def noOverflowFlags : ArithIntegerOverflowFlagsProperties :=
  { attr := { nsw := false, nuw := false } }

/-- Declare an `arith.constant` operation and its value result. -/
@[inline, simp]
def MatchProg.arithConstantValue (returnType : Handle OpCode .type) (expected : Int) :
    MatchProg.Builder (Handle OpCode .value × Handle OpCode .op) := do
  let operation ← MatchProg.operation (.arith .constant) #[] #[returnType]
    (fun actual => actual.value.value = expected)
  return (operation.res[0]!, operation.op)

private def matchAddZero :
    MatchProg OpCode (Handle OpCode .value × Handle OpCode .value × Handle OpCode .op) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value returnType
    let (zero, constantOp) ← MatchProg.arithConstantValue returnType 0
    let _ ← MatchProg.root (.arith .addi) #[x, zero] #[returnType]
    return (x, zero, constantOp)

private def addZero : Pattern OpCode :=
  let (x, _, _) := matchAddZero.exports
  let creation := CreateProg.empty matchAddZero
  {
    Exports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    matcher := matchAddZero
    CreationExports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    creation := creation
    replacement := #[x]
  }

/-- Rewrite `x * 2` to `x + x`. -/
private def mulTwo : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let (two, _) ← MatchProg.arithConstantValue returnType 2
      let _ ← MatchProg.root (.arith .muli) #[x, two] #[returnType]
        (fun actual => !actual.attr.nsw && !actual.attr.nuw)
      return (returnType, x))
    (fun (returnType, x) => do
      let properties ← CreateProg.property (.arith .addi) noOverflowFlags
      let add ← CreateProg.operation (.arith .addi) #[x, x] #[returnType] properties
      return add)
    (fun result => result)

theorem mulTwo_valid : Pattern.Valid mulTwo := by
  puddle_simp [mulTwo]

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
  sorry

theorem nativeApply_valid : Pattern.Valid nativeApply := by
  simp only [nativeApply]
  provePuddleValid
  sorry

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
    %10 = "arith.constant"() <{"value" = 3 : i32}> : () -> i32
    %11 = "arith.addi"(%5, %10) : (i32, i32) -> i32
    "test.test"(%11) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint mulTwoProgram nativeApply
private def resolvedOperation : OperationPtr := ⟨7⟩

private def resolvedOperationHandle : Handle OpCode .op := ⟨0⟩

private def resolvedResultHandles : Array (Handle OpCode .value) := #[⟨1⟩, ⟨2⟩]

private def resolvedAssignment : Assignment OpCode := ⟨#[
  none,
  some (.value (.opResult (resolvedOperation.getResult 0))),
  some (.value (.opResult (resolvedOperation.getResult 1)))
]⟩

example : Assignment.findOp resolvedAssignment resolvedOperationHandle resolvedResultHandles =
    some resolvedOperation := by
  native_decide

private def mismatchedResultAssignment : Assignment OpCode := ⟨#[
  none,
  some (.value (.opResult (resolvedOperation.getResult 0))),
  some (.value (.opResult (resolvedOperation.getResult 0)))
]⟩

example : Assignment.bindValues mismatchedResultAssignment resolvedResultHandles.toList
    #[.opResult (resolvedOperation.getResult 0),
      .opResult (resolvedOperation.getResult 1)].toList = none := by
  native_decide

private def rootWithTwoResults := MatchProg.build do
  let root ← MatchProg.root (.arith .addi) #[]
    #[(⟨10⟩ : Handle OpCode .type), ⟨11⟩]
  return root

private def getOperationResultIds (decl : MatchDecl OpCode) : Array Nat :=
  match decl with
  | .operation _ _ _ _ _ _ results _ => results.map (fun result => result.id)
  | _ => #[]

example : rootWithTwoResults.numHandles = 4 := by
  native_decide

example : rootWithTwoResults.rootHandle = rootWithTwoResults.exports.op := by
  native_decide

example : rootWithTwoResults.rootResults?.map (fun results =>
    results.map (fun result => result.id)) = some #[1, 2] := by
  native_decide

example : rootWithTwoResults.decls.length = 1 := by
  native_decide

example : rootWithTwoResults.exports.properties.id = 3 := by
  native_decide

example : rootWithTwoResults.decls[0]?.map getOperationResultIds = some #[1, 2] := by
  native_decide

example : (rootWithTwoResults.collectBindings.bind fun defined =>
    guard (defined.require rootWithTwoResults.rootHandle)) = none := by
  native_decide

example : (rootWithTwoResults.rootResults?.bind fun results =>
    rootWithTwoResults.collectBindings.bind fun defined =>
      guard (defined.require results[0]!)) = none := by
  native_decide

private theorem addZero_valid : addZero.Valid := by
  puddle_simp [addZero]

private def guardedAddZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value returnType
      let (zero, _) ← MatchProg.arithConstantValue returnType 0
      let root ← MatchProg.root (.arith .addi) #[lhs, zero] #[returnType]
      let _ ← MatchProg.matchNative (returnType, root.properties) fun (_, prop) =>
        prop.attr.nsw = true
      return lhs)
    pure
    (fun result => result)

private theorem guardedAddZero_valid : guardedAddZero.Valid := by
  puddle_simp [guardedAddZero]

/-- A root with two results can be replaced by an array of two matched values. -/
private def replaceTwoResults : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let y ← MatchProg.value returnType
      let _ ← MatchProg.root (.arith .addi) #[x, y] #[returnType, returnType]
      return (x, y))
    (fun values => pure values)
    (fun (x, y) => #[x, y])

/-! A one-operation creation rule: clone a matched `arith.addi` and replace the old result with
the freshly-created result. The deliberately simple `rfl`-level algebraic proof is a regression
for the author-facing validity boundary. -/

private abbrev matchCloneAdd :
    MatchProg OpCode (Handle OpCode .type × Handle OpCode .value × Handle OpCode .value) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let lhs ← MatchProg.value returnType
    let rhs ← MatchProg.value returnType
    let _ ← MatchProg.root (.arith .addi) #[lhs, rhs] #[returnType]
      (fun actual => !actual.attr.nsw && !actual.attr.nuw)
    return (returnType, lhs, rhs)

private abbrev cloneAddCreation : CreateProg OpCode (Handle OpCode .value) :=
  CreateProg.build matchCloneAdd fun (returnType, lhs, rhs) => do
    let properties ← CreateProg.property (.arith .addi) noOverflowFlags
    let operation ← CreateProg.operation (.arith .addi)
      #[lhs, rhs]
      #[returnType]
      properties
    return operation.res[0]!

private example :
    (matchCloneAdd.collectBindings.bind cloneAddCreation.checkBindings).isSome := by
  native_decide

private def nonFreshCloneAddCreation : CreateProg OpCode Unit :=
  {
    decls := [
      .property (.arith .addi) noOverflowFlags
        ⟨0⟩
    ]
    numHandles := matchCloneAdd.numHandles + 2
    exports := ()
  }

private example :
    ¬(matchCloneAdd.collectBindings.bind nonFreshCloneAddCreation.checkBindings).isSome := by
  native_decide

private def forwardReferenceCloneAddCreation : CreateProg OpCode Unit :=
  let (returnType, lhs, rhs) := matchCloneAdd.exports
  {
    decls := [
      .operation (.arith .addi) #[lhs, rhs] #[returnType]
        ⟨matchCloneAdd.numHandles⟩
        ⟨matchCloneAdd.numHandles + 1⟩
        #[⟨matchCloneAdd.numHandles + 2⟩],
      .property (.arith .addi) noOverflowFlags
        ⟨matchCloneAdd.numHandles⟩
    ]
    numHandles := matchCloneAdd.numHandles + 3
    exports := ()
  }

private example :
    ¬(matchCloneAdd.collectBindings.bind forwardReferenceCloneAddCreation.checkBindings).isSome := by
  native_decide

private def cloneAdd : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value returnType
      let rhs ← MatchProg.value returnType
      let _ ← MatchProg.root (.arith .addi) #[lhs, rhs] #[returnType]
        (fun actual => !actual.attr.nsw && !actual.attr.nuw)
      return (returnType, lhs, rhs))
    (fun (returnType, lhs, rhs) => do
      let properties ← CreateProg.property (.arith .addi) noOverflowFlags
      let operation ← CreateProg.operation (.arith .addi)
        #[lhs, rhs]
        #[returnType]
        properties
      return operation.res[0]!)
    (fun value => value)

private abbrev cloneAddExpanded : Pattern OpCode :=
  let creation := cloneAddCreation
  {
    Exports := Handle OpCode .type × Handle OpCode .value × Handle OpCode .value
    matcher := matchCloneAdd
    CreationExports := Handle OpCode .value
    creation := creation
    replacement := creation.exports
  }

set_option maxHeartbeats 800000 in
private theorem cloneAdd_valid : cloneAdd.Valid := by
  puddle_simp [cloneAdd]

private example : cloneAdd = cloneAddExpanded := rfl

private example :
    cloneAddCreation.exports.id = matchCloneAdd.numHandles + 2 := by
  native_decide

/-- Regression rule showing that creation no longer falls back to operand-based type inference. -/
private abbrev cloneAddWithoutResultTypesCreation : CreateProg OpCode Unit :=
  CreateProg.build matchCloneAdd fun (_, lhs, rhs) => do
    let properties ← CreateProg.property (.arith .addi) noOverflowFlags
    let _ ← CreateProg.operation (.arith .addi)
      #[lhs, rhs]
      #[]
      properties
    return ()

private def cloneAddWithoutResultTypes : Pattern OpCode :=
  let creation := cloneAddWithoutResultTypesCreation
  {
    Exports := Handle OpCode .type × Handle OpCode .value × Handle OpCode .value
    matcher := matchCloneAdd
    CreationExports := Unit
    creation := creation
    replacement := (⟨6⟩ : Handle OpCode .value)
  }

/-! A creation program is an ordered DSL: the second declaration below consumes the result handle
exported by the first declaration. -/

private abbrev matchDoubleAdd :
    MatchProg OpCode (Handle OpCode .type × Handle OpCode .value × Handle OpCode .value) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let lhs ← MatchProg.value returnType
    let rhs ← MatchProg.value returnType
    let inner ← MatchProg.operation (.arith .addi) #[lhs, rhs] #[returnType]
      (fun actual => !actual.attr.nsw && !actual.attr.nuw)
    let _ ← MatchProg.root (.arith .addi) #[inner.res[0]!, inner.res[0]!] #[returnType]
      (fun actual => !actual.attr.nsw && !actual.attr.nuw)
    return (returnType, lhs, rhs)

private abbrev doubleAddCreation : CreateProg OpCode (Handle OpCode .value) :=
  CreateProg.build matchDoubleAdd fun (returnType, lhs, rhs) => do
    let firstProperties ← CreateProg.property (.arith .addi) noOverflowFlags
    let first ← CreateProg.operation (.arith .addi)
      #[lhs, rhs]
      #[returnType]
      firstProperties
    let secondProperties ← CreateProg.property (.arith .addi) noOverflowFlags
    let second ← CreateProg.operation (.arith .addi)
      #[first.res[0]!, first.res[0]!]
      #[returnType]
      secondProperties
    return second.res[0]!

private def doubleAdd : Pattern OpCode :=
  let creation := doubleAddCreation
  {
    Exports := Handle OpCode .type × Handle OpCode .value × Handle OpCode .value
    matcher := matchDoubleAdd
    CreationExports := Handle OpCode .value
    creation := creation
    replacement := creation.exports
  }

private example :
    (matchDoubleAdd.collectBindings.bind doubleAddCreation.checkBindings).isSome := by
  native_decide

set_option maxHeartbeats 800000 in
private theorem doubleAdd_valid : doubleAdd.Valid := by
  puddle_simp [doubleAdd]
  all_goals simp_all [SemanticAssignment.bindValue, SemanticAssignment.bindValues]
  all_goals rw [SemanticAssignment.getValue_bind_value_id]
  all_goals simp [RuntimeValue.arrayIsRefinedBy_refl]

private example :
    doubleAddCreation.decls.length = 4 := by native_decide

private def firstOperationOperand : CreateDecl OpCode → Option (Handle OpCode .value)
  | .operation _ operands _ _ _ _ => operands[0]?
  | .type _ _ => none
  | .property _ _ _ => none
  | @CreateDecl.applyNative _ _ _ _ _ _ _ _ _ => none

private example :
    doubleAddCreation.decls[3]?.bind firstOperationOperand =
      some ⟨11⟩ := by native_decide

private def matchSubZero :
    MatchProg OpCode (Handle OpCode .value × Handle OpCode .value × Handle OpCode .op) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value returnType
    let (zero, constantOp) ← MatchProg.arithConstantValue returnType 0
    let _ ← MatchProg.root (.arith .subi) #[x, zero] #[returnType]
    return (x, zero, constantOp)

private def subZero : Pattern OpCode :=
  let (x, _, _) := matchSubZero.exports
  let creation := CreateProg.empty matchSubZero
  {
    Exports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    matcher := matchSubZero
    CreationExports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    creation := creation
    replacement := x
  }

private theorem subZero_valid : subZero.Valid := by
  puddle_simp [subZero]

private def matchMulOne :
    MatchProg OpCode (Handle OpCode .value × Handle OpCode .value × Handle OpCode .op) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value returnType
    let (one, constantOp) ← MatchProg.arithConstantValue returnType 1
    let _ ← MatchProg.root (.arith .muli) #[x, one] #[returnType]
    return (x, one, constantOp)

private def mulOne : Pattern OpCode :=
  let (x, _, _) := matchMulOne.exports
  let creation := CreateProg.empty matchMulOne
  {
    Exports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    matcher := matchMulOne
    CreationExports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    creation := creation
    replacement := x
  }

private theorem mulOne_valid : mulOne.Valid := by
  puddle_simp [mulOne]

private def matchMulZero :
    MatchProg OpCode (Handle OpCode .value × Handle OpCode .value × Handle OpCode .op) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value returnType
    let (zero, constantOp) ← MatchProg.arithConstantValue returnType 0
    let _ ← MatchProg.root (.arith .muli) #[x, zero] #[returnType]
    return (x, zero, constantOp)

private def mulZero : Pattern OpCode :=
  let (_, zero, _) := matchMulZero.exports
  let creation := CreateProg.empty matchMulZero
  {
    Exports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    matcher := matchMulZero
    CreationExports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    creation := creation
    replacement := zero
  }

private theorem mulZero_valid : mulZero.Valid := by
  puddle_simp [mulZero]

private def i32Type : IntegerType := IntegerType.mk 32

private def i32 : TypeAttr := i32Type

private def matcherAccepts (builder : MatchProg.Builder (Handle OpCode .type))
    (type : TypeAttr) : Bool :=
  let (_, state) := builder.run {}
  match state.decls with
  | [.type matcher _] => matcher type
  | _ => false

private def floatMatcher := MatchProg.type (Attr := FloatType)
private def byteMatcher := MatchProg.type (Attr := LLVM.ByteType)
private def modArithMatcher := MatchProg.type (Attr := ModArithType)
private def registerMatcher := MatchProg.type (Attr := RegisterType)
private def pointerMatcher := MatchProg.type (Attr := LLVM.PointerType)

#guard matcherAccepts floatMatcher (FloatType.mk 32)
#guard matcherAccepts byteMatcher (LLVM.ByteType.mk 8)
#guard matcherAccepts modArithMatcher (ModArithType.mk (IntegerAttr.mk 17 i32Type))
#guard matcherAccepts registerMatcher (RegisterType.mk none)
#guard matcherAccepts pointerMatcher LLVM.PointerType.mk
#guard !(matcherAccepts floatMatcher i32)
#guard !(matcherAccepts pointerMatcher (FloatType.mk 64))

private def matchAddZeroI32 :
    MatchProg OpCode (Handle OpCode .value × Handle OpCode .value × Handle OpCode .op) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType) (fun actual => actual == i32Type)
    let x ← MatchProg.value returnType
    let (zero, constantOp) ← MatchProg.arithConstantValue returnType 0
    let _ ← MatchProg.root (.arith .addi) #[x, zero] #[returnType]
    return (x, zero, constantOp)

private def addZeroI32 : Pattern OpCode :=
  let (x, _, _) := matchAddZeroI32.exports
  let creation := CreateProg.empty matchAddZeroI32
  {
    Exports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    matcher := matchAddZeroI32
    CreationExports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    creation := creation
    replacement := x
  }

private def matchAddZeroNonI32 :
    MatchProg OpCode (Handle OpCode .value × Handle OpCode .value × Handle OpCode .op) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType) (fun actual => actual != i32Type)
    let x ← MatchProg.value returnType
    let (zero, constantOp) ← MatchProg.arithConstantValue returnType 0
    let _ ← MatchProg.root (.arith .addi) #[x, zero] #[returnType]
    return (x, zero, constantOp)

private def addZeroNonI32 : Pattern OpCode :=
  let (x, _, _) := matchAddZeroNonI32.exports
  let creation := CreateProg.empty matchAddZeroNonI32
  {
    Exports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    matcher := matchAddZeroNonI32
    CreationExports := Handle OpCode .value × Handle OpCode .value × Handle OpCode .op
    creation := creation
    replacement := x
  }

private structure CompileFixture where
  ctx : WfIRContext OpCode
  root : OperationPtr
  x : ValuePtr

private def freshBlockArgs (numArgs : Nat) : WfIRContext OpCode × Array ValuePtr :=
  let (ctx, _) := WfIRContext.create! OpCode
  let (ctx, block) := WfRewriter.createBlock! ctx (Array.replicate numArgs i32) none
  (ctx, block.getArguments! ctx.raw)

private def createConstant (ctx : WfIRContext OpCode) (value : Int) :
    WfIRContext OpCode × OperationPtr :=
  let properties : ArithConstantProperties := { value := IntegerAttr.mk value i32Type }
  (WfRewriter.createOp! ctx Arith.constant #[i32] #[] #[] #[]
    properties none).get!

private def createBinaryOp (ctx : WfIRContext OpCode) (opCode : Arith)
    (lhs rhs : ValuePtr) : WfIRContext OpCode × OperationPtr :=
  (WfRewriter.createOp! ctx opCode #[i32] #[lhs, rhs] #[] #[] default none).get!

private def successFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 1
  let x := args[0]!
  let (ctx, zero) := createConstant ctx 0
  let (ctx, root) := createBinaryOp ctx .addi x (zero.getResult 0)
  ⟨ctx, root, x⟩

private def guardedAddPredicate (accept : Bool)
    (input : TypeAttr × ArithIntegerOverflowFlagsProperties) : Bool :=
  let (actualType, actualProperties) := input
  actualType == i32 &&
    actualProperties == (default : ArithIntegerOverflowFlagsProperties) && accept

private def matchGuardedAdd (accept : Bool) : MatchProg OpCode Unit :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let lhs ← MatchProg.value returnType
    let rhs ← MatchProg.value returnType
    let root ← MatchProg.root (.arith .addi) #[lhs, rhs] #[returnType]
    let _ ← MatchProg.matchNative (returnType, root.properties) (guardedAddPredicate accept)
    return ()

private def nativeGuardAccepts (fixture : CompileFixture) : Bool :=
  (matchGuardedAdd true).run fixture.ctx.raw fixture.root |>.isSome

private def nativeGuardRejects (fixture : CompileFixture) : Bool :=
  (matchGuardedAdd false).run fixture.ctx.raw fixture.root |>.isNone

private def subZeroSuccessFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 1
  let x := args[0]!
  let (ctx, zero) := createConstant ctx 0
  let (ctx, root) := createBinaryOp ctx .subi x (zero.getResult 0)
  ⟨ctx, root, x⟩

private def mulOneSuccessFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 1
  let x := args[0]!
  let (ctx, one) := createConstant ctx 1
  let (ctx, root) := createBinaryOp ctx .muli x (one.getResult 0)
  ⟨ctx, root, x⟩

private def wrongRootOpcodeFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 1
  let x := args[0]!
  let (ctx, zero) := createConstant ctx 0
  let (ctx, root) := createBinaryOp ctx .muli x (zero.getResult 0)
  ⟨ctx, root, x⟩

private def wrongOperandCountFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 1
  let x := args[0]!
  let (ctx, root) :=
    (WfRewriter.createOp! ctx Arith.addi #[i32] #[x] #[] #[] default none).get!
  ⟨ctx, root, x⟩

private def noDefiningOpFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 2
  let x := args[0]!
  let (ctx, root) := createBinaryOp ctx .addi x args[1]!
  ⟨ctx, root, x⟩

private def wrongDefiningOpcodeFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 1
  let x := args[0]!
  let (ctx, product) := createBinaryOp ctx .muli x x
  let (ctx, root) := createBinaryOp ctx .addi x (product.getResult 0)
  ⟨ctx, root, x⟩

private def nonzeroConstantFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 1
  let x := args[0]!
  let (ctx, one) := createConstant ctx 1
  let (ctx, root) := createBinaryOp ctx .addi x (one.getResult 0)
  ⟨ctx, root, x⟩

/-- Check a match-and-replace-only result without comparing proof-carrying `WfIRContext`s. -/
private def sameContextShape (lhs rhs : WfIRContext OpCode) : Bool :=
  lhs.raw.nextID == rhs.raw.nextID &&
    lhs.raw.operations.size == rhs.raw.operations.size &&
    lhs.raw.blocks.size == rhs.raw.blocks.size &&
    lhs.raw.regions.size == rhs.raw.regions.size

private def compilesSuccessfully (rule : Pattern OpCode) (fixture : CompileFixture) : Bool :=
  match rule.interpret fixture.ctx fixture.root with
  | some (ctx, some (newOps, newValues)) =>
    sameContextShape ctx fixture.ctx && newOps.isEmpty && newValues == #[fixture.x]
  | _ => false

private def leavesContextUnchangedWithoutMatch (fixture : CompileFixture) : Bool :=
  match addZero.interpret fixture.ctx fixture.root with
  | some (ctx, none) => sameContextShape ctx fixture.ctx
  | _ => false

private def typeMatcherRejects (fixture : CompileFixture) : Bool :=
  match addZeroNonI32.interpret fixture.ctx fixture.root with
  | some (ctx, none) => sameContextShape ctx fixture.ctx
  | _ => false

/-- The creation phase allocates one `arith.addi`, returns it in `newOps`, and selects its result. -/
private def createsCloneAdd (fixture : CompileFixture) : Bool :=
  match cloneAdd.interpret fixture.ctx fixture.root with
  | some (ctx, some (newOps, newValues)) =>
    match newOps.toList with
    | [newOp] =>
      ctx.raw.operations.size == fixture.ctx.raw.operations.size + 1 &&
        ctx.raw.blocks.size == fixture.ctx.raw.blocks.size &&
        ctx.raw.regions.size == fixture.ctx.raw.regions.size &&
        newValues == #[.opResult (newOp.getResult 0)] &&
        newOp.getOpType! ctx.raw == OpCode.arith .addi &&
        newOp.getResultTypes! ctx.raw == #[i32] &&
        newOp.getOperands! ctx.raw == fixture.root.getOperands! fixture.ctx.raw
    | _ => false
  | _ => false

private def rejectsCreationWithoutResultTypes (fixture : CompileFixture) : Bool :=
  match cloneAddWithoutResultTypes.interpret fixture.ctx fixture.root with
  | none => true
  | _ => false

private def replacesTwoResults : Bool :=
  let (ctx, args) := freshBlockArgs 2
  let x := args[0]!
  let y := args[1]!
  let (ctx, root) :=
    (WfRewriter.createOp! ctx Arith.addi #[i32, i32] #[x, y] #[] #[] default none).get!
  match replaceTwoResults.interpret ctx root with
  | some (newCtx, some (newOps, newValues)) =>
    sameContextShape newCtx ctx && newOps.isEmpty && newValues == #[x, y]
  | _ => false

/-! Native metadata declarations can combine several matched metadata values and feed their
results directly to later native declarations and operation creation. -/

private abbrev AddProps := ArithIntegerOverflowFlagsProperties

/-! A small end-to-end validity example: every `arith.addi` may be recreated with both overflow
flags cleared. The matched property is deliberately consumed by `applyNative`, even though the
native function replaces both fields with constants. -/

private abbrev matchClearAddFlags :
    MatchProg OpCode (Handle OpCode .type × Handle OpCode .value × Handle OpCode .value ×
      Handle OpCode (.prop (.arith .addi))) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let lhs ← MatchProg.value returnType
    let rhs ← MatchProg.value returnType
    let root ← MatchProg.root (.arith .addi) #[lhs, rhs] #[returnType]
    return (returnType, lhs, rhs, root.properties)

@[simp]
private def clearAddFlags
    (_ : AddProps) : Option AddProps :=
  some noOverflowFlags

private abbrev clearAddFlagsCreation : CreateProg OpCode (Handle OpCode .value) :=
  CreateProg.build matchClearAddFlags fun (returnType, lhs, rhs, properties) => do
    let cleared ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.arith .addi))) properties clearAddFlags
    let replacement ← CreateProg.operation (.arith .addi)
      #[lhs, rhs] #[returnType] cleared
    return replacement.res[0]!

private example :
    (matchClearAddFlags.collectBindings.bind clearAddFlagsCreation.checkBindings).isSome := by
  native_decide

private def clearAddFlagsPattern : Pattern OpCode :=
  let creation := clearAddFlagsCreation
  {
    Exports := Handle OpCode .type × Handle OpCode .value × Handle OpCode .value ×
      Handle OpCode (.prop (.arith .addi))
    matcher := matchClearAddFlags
    CreationExports := Handle OpCode .value
    creation
    replacement := creation.exports
  }

@[simp]
private theorem addWithFlags_refines_addWithoutFlags {width : Nat}
    (lhs rhs : Data.LLVM.Int width) (nsw nuw : Bool) :
    Data.LLVM.Int.add lhs rhs nsw nuw ⊒
      Data.LLVM.Int.add lhs rhs false false := by
  cases lhs <;> cases rhs <;>
    simp only [Data.LLVM.Int.add, Id.run] <;>
    repeat' first | split | simp [isRefinedBy, pure] | grind

private theorem clearAddFlagsPattern_valid : clearAddFlagsPattern.Valid := by
  puddle_simp [clearAddFlagsPattern]
  all_goals simp [SemanticAssignment.bindProperty, SemanticAssignment.bindValue,
    SemanticAssignment.bindValues]
  all_goals rw [SemanticAssignment.getValue_bind_value_id]
  all_goals simp [addWithFlags_refines_addWithoutFlags]

private def sameNativeMetadata
    (input : TypeAttr × AddProps × TypeAttr × AddProps) : Bool :=
  let (innerType, innerProperties, rootType, rootProperties) := input
  innerType == rootType && innerProperties == rootProperties

private abbrev matchNativeMetadata :
    MatchProg OpCode (Handle OpCode .type × Handle OpCode (.prop (.arith .addi)) ×
      Handle OpCode .type × Handle OpCode (.prop (.arith .addi)) × Handle OpCode .value) :=
  MatchProg.build do
    let innerType ← MatchProg.type (Attr := IntegerType)
    let lhs ← MatchProg.value innerType
    let rhs ← MatchProg.value innerType
    let inner ← MatchProg.operation (.arith .addi) #[lhs, rhs] #[innerType]
    let rootType ← MatchProg.type (Attr := IntegerType)
    let root ← MatchProg.root (.arith .addi)
      #[inner.res[0]!, inner.res[0]!] #[rootType]
    let _ ← MatchProg.matchNative
      (innerType, inner.properties, rootType, root.properties)
      sameNativeMetadata
    return (innerType, inner.properties, rootType, root.properties, inner.res[0]!)

private def combineNativeMetadata
    (input : TypeAttr × AddProps × TypeAttr × AddProps) :
    Option (TypeAttr × AddProps) :=
  let (lhsType, lhsProps, rhsType, rhsProps) := input
  if lhsType == rhsType && lhsProps == rhsProps then
    some (lhsType, {
      attr := {
        nsw := lhsProps.attr.nsw || rhsProps.attr.nsw
        nuw := lhsProps.attr.nuw || rhsProps.attr.nuw
      }
    })
  else none

private abbrev nativeMetadataCreation : CreateProg OpCode (Handle OpCode .value) :=
  CreateProg.build matchNativeMetadata fun
      (innerType, innerProps, rootType, rootProps, innerResult) => do
    let (newType, newProps) ← CreateProg.applyNative
      (Outputs := Handle OpCode .type × Handle OpCode (.prop (.arith .addi)))
      (innerType, innerProps, rootType, rootProps)
      combineNativeMetadata
    let cloned ← CreateProg.operation (.arith .addi)
      #[innerResult, innerResult] #[newType] newProps
    return cloned.res[0]!

private def nativeMetadataClone : Pattern OpCode :=
  let creation := nativeMetadataCreation
  {
    Exports := Handle OpCode .type × Handle OpCode (.prop (.arith .addi)) ×
      Handle OpCode .type × Handle OpCode (.prop (.arith .addi)) × Handle OpCode .value
    matcher := matchNativeMetadata
    CreationExports := Handle OpCode .value
    creation
    replacement := creation.exports
  }

private def nativeFixture : CompileFixture :=
  let (ctx, args) := freshBlockArgs 2
  let lhs := args[0]!
  let rhs := args[1]!
  let (ctx, inner) := createBinaryOp ctx .addi lhs rhs
  let innerResult := inner.getResult 0
  let (ctx, root) := createBinaryOp ctx .addi innerResult innerResult
  ⟨ctx, root, innerResult⟩

private def createsNativeMetadataClone (fixture : CompileFixture) : Bool :=
  match nativeMetadataClone.interpret fixture.ctx fixture.root with
  | some (ctx, some (newOps, newValues)) =>
    match newOps.toList with
    | [newOp] =>
      ctx.raw.operations.size == fixture.ctx.raw.operations.size + 1 &&
        newValues == #[.opResult (newOp.getResult 0)] &&
        newOp.getResultTypes! ctx.raw == #[i32] &&
        newOp.getProperties! ctx.raw (OpCode.arith .addi) == (default : AddProps)
    | _ => false
  | _ => false

private abbrev chainedNativeCreation :
    CreateProg OpCode (Handle OpCode .type × Handle OpCode (.prop (.arith .addi))) :=
  CreateProg.build matchNativeMetadata fun
      (innerType, innerProps, rootType, rootProps, _) => do
    let generatedType ← CreateProg.applyNative
      (Outputs := Handle OpCode .type) () (fun () => some i32)
    let copiedType ← CreateProg.applyNative
      (Outputs := Handle OpCode .type) generatedType some
    let generatedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.arith .addi)))
      (innerType, innerProps, rootType, rootProps)
      (fun input => (combineNativeMetadata input).map Prod.snd)
    let _ ← CreateProg.applyNative (Outputs := Unit)
      (copiedType, generatedProps) (fun _ => some ())
    return (copiedType, generatedProps)

private def nativeCallsChainAndEmitNothing (fixture : CompileFixture) : Bool :=
  match matchNativeMetadata.run fixture.ctx.raw fixture.root with
  | none => false
  | some matched =>
    match chainedNativeCreation.run matched fixture.ctx with
    | some (ctx, operations, assignment) =>
      let (typeHandle, propertyHandle) := chainedNativeCreation.exports
      sameContextShape ctx fixture.ctx && operations.isEmpty &&
        Assignment.getType assignment typeHandle == some i32 &&
        Assignment.getProperty assignment propertyHandle == some (default : AddProps)
    | none => false

private abbrev rejectingNativeCreation : CreateProg OpCode Unit :=
  CreateProg.build matchNativeMetadata fun
      (innerType, innerProps, rootType, rootProps, _) => do
    let _ ← CreateProg.applyNative (Outputs := Unit)
      (innerType, innerProps, rootType, rootProps) (fun _ => none)
    return ()

private def rejectingNative : Pattern OpCode :=
  let creation := rejectingNativeCreation
  {
    Exports := Handle OpCode .type × Handle OpCode (.prop (.arith .addi)) ×
      Handle OpCode .type × Handle OpCode (.prop (.arith .addi)) × Handle OpCode .value
    matcher := matchNativeMetadata
    CreationExports := Unit
    creation
    replacement := matchNativeMetadata.exports.2.2.2.2
  }

private def nativeRejectionIsFatal (fixture : CompileFixture) : Bool :=
  rejectingNative.interpret fixture.ctx fixture.root |>.isNone

private def invalidReplacementIsFatal (fixture : CompileFixture) : Bool :=
  let rule := {
    addZero with replacement := (⟨1000000⟩ : Handle OpCode .value)
  }
  rule.interpret fixture.ctx fixture.root |>.isNone

private example :
    let (typeHandle, propertyHandle) := chainedNativeCreation.exports
    typeHandle.id + 1 = propertyHandle.id ∧ chainedNativeCreation.decls.length = 4 := by
  native_decide

/- Operation and value handles deliberately are not metadata tuples. -/
/-- error: failed to synthesize
  IsMetadataTuple OpCode (Handle OpCode HandleType.op)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth IsMetadataTuple OpCode (Handle OpCode .op)

/-- error: failed to synthesize
  IsMetadataTuple OpCode (Handle OpCode HandleType.value)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth IsMetadataTuple OpCode (Handle OpCode .value)

#guard compilesSuccessfully addZero successFixture
#guard compilesSuccessfully addZeroI32 successFixture
#guard typeMatcherRejects successFixture
#guard nativeGuardAccepts successFixture
#guard nativeGuardRejects successFixture
#guard compilesSuccessfully subZero subZeroSuccessFixture
#guard compilesSuccessfully mulOne mulOneSuccessFixture
#guard createsCloneAdd successFixture
#guard rejectsCreationWithoutResultTypes successFixture
#guard replacesTwoResults
#guard createsNativeMetadataClone nativeFixture
#guard nativeCallsChainAndEmitNothing nativeFixture
#guard nativeRejectionIsFatal nativeFixture
#guard invalidReplacementIsFatal successFixture
#guard leavesContextUnchangedWithoutMatch wrongRootOpcodeFixture
#guard leavesContextUnchangedWithoutMatch wrongOperandCountFixture
#guard leavesContextUnchangedWithoutMatch noDefiningOpFixture
#guard leavesContextUnchangedWithoutMatch wrongDefiningOpcodeFixture
#guard leavesContextUnchangedWithoutMatch nonzeroConstantFixture

/-! Proof-level regressions for the generic semantic bridge. -/

example
    (hOps : addZero.interpret.ReturnOps)
    (hCtx : addZero.interpret.ReturnCtxChanges)
    (hBounds : addZero.interpret.ReturnValuesInBounds)
    (hValues : addZero.interpret.ReturnValues) :
    addZero.interpret.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics addZero_valid hOps hCtx hBounds hValues

example
    (hOps : clearAddFlagsPattern.interpret.ReturnOps)
    (hCtx : clearAddFlagsPattern.interpret.ReturnCtxChanges)
    (hBounds : clearAddFlagsPattern.interpret.ReturnValuesInBounds)
    (hValues : clearAddFlagsPattern.interpret.ReturnValues) :
    clearAddFlagsPattern.interpret.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics clearAddFlagsPattern_valid hOps hCtx hBounds hValues

example
    (hOps : subZero.interpret.ReturnOps)
    (hCtx : subZero.interpret.ReturnCtxChanges)
    (hBounds : subZero.interpret.ReturnValuesInBounds)
    (hValues : subZero.interpret.ReturnValues) :
    subZero.interpret.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics subZero_valid hOps hCtx hBounds hValues

example
    (hOps : mulOne.interpret.ReturnOps)
    (hCtx : mulOne.interpret.ReturnCtxChanges)
    (hBounds : mulOne.interpret.ReturnValuesInBounds)
    (hValues : mulOne.interpret.ReturnValues) :
    mulOne.interpret.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics mulOne_valid hOps hCtx hBounds hValues

example
    (hOps : mulZero.interpret.ReturnOps)
    (hCtx : mulZero.interpret.ReturnCtxChanges)
    (hBounds : mulZero.interpret.ReturnValuesInBounds)
    (hValues : mulZero.interpret.ReturnValues) :
    mulZero.interpret.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics mulZero_valid hOps hCtx hBounds hValues

private def matchUnsupportedAndi : MatchProg OpCode (Handle OpCode .value) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value returnType
    let _ ← MatchProg.root (.arith .andi) #[x, x] #[returnType]
    return x

/-- Support is derived entirely from effect metadata, including for rewrite roots. -/
example : SupportedOpCode (OpCode.arith .andi) := by
  constructor
  · native_decide
  · intro actual
    simp [OpCode.arith_getEffects_eq_none .andi actual]

private def unsupportedAndi : Pattern OpCode :=
  let x := matchUnsupportedAndi.exports
  let creation := CreateProg.empty matchUnsupportedAndi
  {
    Exports := Handle OpCode .value
    matcher := matchUnsupportedAndi
    CreationExports := Handle OpCode .value
    creation := creation
    replacement := x
  }

/-- An effect-free, non-terminating opcode needs no dedicated validity case. -/
example : unsupportedAndi.Valid := by
  puddle_simp [unsupportedAndi]
