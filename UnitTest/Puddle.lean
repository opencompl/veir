import Veir.PatternRewriter.Puddle
import Veir.Data.LLVM.Int.Lemmas

open Veir
open Veir.Puddle

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
    replacement := .ofValue x
  }

private theorem addZero_valid : addZero.Valid := by
  puddle_simp [addZero]
  simp_all [Interp]

private def guardedAddZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value returnType
      let (zero, _) ← MatchProg.arithConstantValue returnType 0
      let root ← MatchProg.root (.arith .addi) #[lhs, zero] #[returnType]
      let _ ← MatchProg.guard (returnType, root.properties) fun (_, prop) =>
        prop.attr.nsw = true
      return lhs)
    pure
    Replacement.ofValue

private theorem guardedAddZero_valid : guardedAddZero.Valid := by
  puddle_simp [guardedAddZero]
  simp_all [Interp]

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
    let operation ← CreateProg.operation (.arith .addi)
      #[lhs, rhs]
      #[returnType]
      noOverflowFlags
    return operation.res[0]!

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
      let operation ← CreateProg.operation (.arith .addi)
        #[lhs, rhs]
        #[returnType]
        noOverflowFlags
      return operation.res[0]!)
    Replacement.ofValue

private abbrev cloneAddExpanded : Pattern OpCode :=
  let creation := cloneAddCreation
  {
    Exports := Handle OpCode .type × Handle OpCode .value × Handle OpCode .value
    matcher := matchCloneAdd
    CreationExports := Handle OpCode .value
    creation := creation
    replacement := .ofValue creation.exports
  }

private theorem cloneAdd_valid : cloneAdd.Valid := by
  puddle_simp [cloneAdd]
  intro _ lhs rhs flags hnsw hnuw _
  simp_all

private example : cloneAdd = cloneAddExpanded := rfl

private example :
    let creation := cloneAddCreation
    creation.firstHandleId = matchCloneAdd.numHandles ∧
      creation.exports.id = matchCloneAdd.numHandles + 1 := by
  native_decide

/-- Regression rule showing that creation no longer falls back to operand-based type inference. -/
private abbrev cloneAddWithoutResultTypesCreation : CreateProg OpCode Unit :=
  CreateProg.build matchCloneAdd fun (_, lhs, rhs) => do
    let _ ← CreateProg.operation (.arith .addi)
      #[lhs, rhs]
      #[]
      noOverflowFlags
    return ()

private def cloneAddWithoutResultTypes : Pattern OpCode :=
  let creation := cloneAddWithoutResultTypesCreation
  {
    Exports := Handle OpCode .type × Handle OpCode .value × Handle OpCode .value
    matcher := matchCloneAdd
    CreationExports := Unit
    creation := creation
    replacement := .ofValue ⟨6⟩
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
    let first ← CreateProg.operation (.arith .addi)
      #[lhs, rhs]
      #[returnType]
      noOverflowFlags
    let second ← CreateProg.operation (.arith .addi)
      #[first.res[0]!, first.res[0]!]
      #[returnType]
      noOverflowFlags
    return second.res[0]!

private def doubleAdd : Pattern OpCode :=
  let creation := doubleAddCreation
  {
    Exports := Handle OpCode .type × Handle OpCode .value × Handle OpCode .value
    matcher := matchDoubleAdd
    CreationExports := Handle OpCode .value
    creation := creation
    replacement := .ofValue creation.exports
  }

set_option maxHeartbeats 800000 in
private theorem doubleAdd_valid : doubleAdd.Valid := by
  puddle_simp [doubleAdd]
  intro _ lhs rhs innerFlags hInnerNsw hInnerNuw _
  intro rootFlags hRootNsw hRootNuw _
  simp_all

private example :
    doubleAddCreation.decls.length = 2 := by native_decide

private def firstCreateOperand : CreateDecl OpCode → Option (CreateOperand OpCode)
  | .operation _ operands _ _ _ _ => operands[0]?
  | @CreateDecl.applyNative _ _ _ _ _ _ _ _ _ => none

private example :
    doubleAddCreation.decls[1]?.bind firstCreateOperand =
      some ⟨⟨9⟩⟩ := by native_decide

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
    replacement := .ofValue x
  }

private theorem subZero_valid : subZero.Valid := by
  puddle_simp [subZero]
  intro _ value constant hconstant _ flags _
  simp_all

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
    replacement := .ofValue x
  }

private theorem mulOne_valid : mulOne.Valid := by
  puddle_simp [mulOne]
  intro _ value constant hconstant _ flags _
  simp_all

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
    replacement := .ofValue zero
  }

private theorem mulZero_valid : mulZero.Valid := by
  puddle_simp [mulZero]
  intro _ value constant hconstant _ flags _
  simp_all

private def i32Type : IntegerType := IntegerType.mk 32

private def i32 : TypeAttr := i32Type

private def matcherAccepts (prog : MatchProg OpCode (Handle OpCode .type))
    (type : TypeAttr) : Bool :=
  match prog.decls with
  | [.type matcher _] => matcher type
  | _ => false

private def floatMatcher := MatchProg.build (MatchProg.type (Attr := FloatType))
private def byteMatcher := MatchProg.build (MatchProg.type (Attr := LLVM.ByteType))
private def modArithMatcher := MatchProg.build (MatchProg.type (Attr := ModArithType))
private def registerMatcher := MatchProg.build (MatchProg.type (Attr := RegisterType))
private def pointerMatcher := MatchProg.build (MatchProg.type (Attr := LLVM.PointerType))

#guard matcherAccepts floatMatcher (FloatType.mk 32)
#guard matcherAccepts byteMatcher (LLVM.ByteType.mk 8)
#guard matcherAccepts modArithMatcher (ModArithType.mk (IntegerAttr.mk 17 i32Type))
#guard matcherAccepts registerMatcher (RegisterType.mk none)
#guard matcherAccepts pointerMatcher LLVM.PointerType.mk
#guard !(matcherAccepts floatMatcher i32)
#guard !(matcherAccepts pointerMatcher (FloatType.mk 64))

/-- A type matcher ranges over every type accepted by its predicate. -/
private example (assignment : SemanticAssignment) (handle : Handle OpCode .type)
    (next : SemanticAssignment → Prop) :
    MatchDecl.denote (.type (fun _ => true) handle) assignment next ↔
      (∀ type, next (assignment.bindType handle type)) := by
  simp [MatchDecl.denote, TypeMatcher.denote]

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
    replacement := .ofValue x
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
    replacement := .ofValue x
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
    let _ ← MatchProg.guard (returnType, root.properties) (guardedAddPredicate accept)
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
  match rule.compile fixture.ctx fixture.root with
  | some (ctx, some (newOps, newValues)) =>
    sameContextShape ctx fixture.ctx && newOps.isEmpty && newValues == #[fixture.x]
  | _ => false

private def leavesContextUnchangedWithoutMatch (fixture : CompileFixture) : Bool :=
  match addZero.compile fixture.ctx fixture.root with
  | some (ctx, none) => sameContextShape ctx fixture.ctx
  | _ => false

private def typeMatcherRejects (fixture : CompileFixture) : Bool :=
  match addZeroNonI32.compile fixture.ctx fixture.root with
  | some (ctx, none) => sameContextShape ctx fixture.ctx
  | _ => false

/-- The creation phase allocates one `arith.addi`, returns it in `newOps`, and selects its result. -/
private def createsCloneAdd (fixture : CompileFixture) : Bool :=
  match cloneAdd.compile fixture.ctx fixture.root with
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
  match cloneAddWithoutResultTypes.compile fixture.ctx fixture.root with
  | none => true
  | _ => false

private def replacesTwoResults : Bool :=
  let (ctx, args) := freshBlockArgs 2
  let x := args[0]!
  let y := args[1]!
  let (ctx, root) :=
    (WfRewriter.createOp! ctx Arith.addi #[i32, i32] #[x, y] #[] #[] default none).get!
  match replaceTwoResults.compile ctx root with
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

private def clearAddFlagsPattern : Pattern OpCode :=
  let creation := clearAddFlagsCreation
  {
    Exports := Handle OpCode .type × Handle OpCode .value × Handle OpCode .value ×
      Handle OpCode (.prop (.arith .addi))
    matcher := matchClearAddFlags
    CreationExports := Handle OpCode .value
    creation
    replacement := .ofValue creation.exports
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
    let _ ← MatchProg.guard
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
    replacement := .ofValue creation.exports
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
  match nativeMetadataClone.compile fixture.ctx fixture.root with
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
    replacement := .ofValue matchNativeMetadata.exports.2.2.2.2
  }

private def nativeRejectionIsFatal (fixture : CompileFixture) : Bool :=
  rejectingNative.compile fixture.ctx fixture.root |>.isNone

private def invalidReplacementIsFatal (fixture : CompileFixture) : Bool :=
  let rule : Pattern OpCode := {
    Exports := Handle OpCode .type × Handle OpCode (.prop (.arith .addi)) ×
      Handle OpCode .type × Handle OpCode (.prop (.arith .addi)) × Handle OpCode .value
    matcher := matchNativeMetadata
    CreationExports := Unit
    creation := CreateProg.build matchNativeMetadata fun _ => pure ()
    replacement := .ofValue ⟨1000000⟩
  }
  rule.compile fixture.ctx fixture.root |>.isNone

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
#guard invalidReplacementIsFatal nativeFixture
#guard leavesContextUnchangedWithoutMatch wrongRootOpcodeFixture
#guard leavesContextUnchangedWithoutMatch wrongOperandCountFixture
#guard leavesContextUnchangedWithoutMatch noDefiningOpFixture
#guard leavesContextUnchangedWithoutMatch wrongDefiningOpcodeFixture
#guard leavesContextUnchangedWithoutMatch nonzeroConstantFixture

/-! Proof-level regressions for the generic semantic bridge. -/

example
    (hOps : addZero.compile.ReturnOps)
    (hCtx : addZero.compile.ReturnCtxChanges)
    (hBounds : addZero.compile.ReturnValuesInBounds)
    (hValues : addZero.compile.ReturnValues) :
    addZero.compile.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics addZero_valid hOps hCtx hBounds hValues

example
    (hOps : clearAddFlagsPattern.compile.ReturnOps)
    (hCtx : clearAddFlagsPattern.compile.ReturnCtxChanges)
    (hBounds : clearAddFlagsPattern.compile.ReturnValuesInBounds)
    (hValues : clearAddFlagsPattern.compile.ReturnValues) :
    clearAddFlagsPattern.compile.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics clearAddFlagsPattern_valid hOps hCtx hBounds hValues

example
    (hOps : subZero.compile.ReturnOps)
    (hCtx : subZero.compile.ReturnCtxChanges)
    (hBounds : subZero.compile.ReturnValuesInBounds)
    (hValues : subZero.compile.ReturnValues) :
    subZero.compile.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics subZero_valid hOps hCtx hBounds hValues

example
    (hOps : mulOne.compile.ReturnOps)
    (hCtx : mulOne.compile.ReturnCtxChanges)
    (hBounds : mulOne.compile.ReturnValuesInBounds)
    (hValues : mulOne.compile.ReturnValues) :
    mulOne.compile.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics mulOne_valid hOps hCtx hBounds hValues

example
    (hOps : mulZero.compile.ReturnOps)
    (hCtx : mulZero.compile.ReturnCtxChanges)
    (hBounds : mulZero.compile.ReturnValuesInBounds)
    (hValues : mulZero.compile.ReturnValues) :
    mulZero.compile.PreservesSemantics hOps hCtx hBounds hValues :=
  Pattern.Valid.preservesSemantics mulZero_valid hOps hCtx hBounds hValues

private def matchUnsupportedAndi : MatchProg OpCode (Handle OpCode .value) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value returnType
    let _ ← MatchProg.root (.arith .andi) #[x, x] #[returnType]
    return x

/-- Support is derived entirely from effect metadata, including for rewrite roots. -/
example : PropertyMatcher.Supported (opCode := .arith .andi) (fun _ => true) 2 1 := by
  refine ⟨rfl, ?_⟩
  intro actual _
  simp [OpCode.arith_getEffects_eq_none .andi actual]

private def unsupportedAndi : Pattern OpCode :=
  let x := matchUnsupportedAndi.exports
  let creation := CreateProg.empty matchUnsupportedAndi
  {
    Exports := Handle OpCode .value
    matcher := matchUnsupportedAndi
    CreationExports := Handle OpCode .value
    creation := creation
    replacement := .ofValue x
  }

/-- An effect-free, non-terminating opcode needs no dedicated validity case. -/
example : unsupportedAndi.Valid := by
  puddle_simp [unsupportedAndi]
  intro _ value actual result successors memory controlFlow hinterpret
  simp [interpretOp', Arith.interpretOp', bind, pure, Interp] at hinterpret
  cases value <;> simp_all
