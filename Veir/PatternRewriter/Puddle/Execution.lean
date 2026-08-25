module

public import Veir.PatternRewriter.Puddle.Definitions
public import Veir.PatternRewriter.Basic

import all Veir.IR.Basic

/-!
# Execution of Puddle Patterns

This file defines the runtime representation and execution of a Puddle pattern. It matches a pattern
against a root operation, creates replacement operations, resolves replacement values, and compiles
the complete rule to the local rewrite-pattern interface.
-/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Assignment and Bindings

This section defines the runtime representation of a Puddle pattern match, which consists of an
assignment of handles (`Assignment`) to concrete IR entities (`Binding`).

Note that the assignment between handles and IR entities does not prevent a handle from being bound
to a different kind of entity than its handle type. So, each getter need to check that the binding
is of the expected kind, and return `none` if it is not. This is a design choice to keep the
assignment representation simple and uniform, at the cost of some runtime checks that should be
eliminated by the compiler when the pattern is known at compile time.
-/

/-- Runtime values bound by Puddle handles. -/
inductive Binding (OpInfo : Type) [HasOpInfo OpInfo] where
| op (operation : OperationPtr)
| value (value : ValuePtr)
| type (type : TypeAttr)
| property (opCode : OpInfo) (value : propertiesOf opCode)
deriving DecidableEq

/--
Runtime bindings associating handles (with their IDs) to concrete IR entities.

Its data structure is an array of optional bindings, where the index corresponds to the handle ID.
This is equivalent to a map from handle IDs to bindings, but is more efficient for the case where
the handle IDs are dense, which is the common case when building Puddle patterns. The array is
extended as needed when new handles are created, and out-of-bounds accesses are treated as unbound
handles.
-/
structure Assignment (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- Slots allocated by the matcher and extended as creation introduces new handles. -/
  bindings : Array (Option (Binding OpInfo))

namespace Assignment

/-- An empty assignment with a specified number of pre-allocated slots for handles. -/
@[expose]
def empty (OpInfo : Type) [HasOpInfo OpInfo] (size : Nat := 0) : Assignment OpInfo :=
  ⟨Array.replicate size none⟩

/-- Get the binding for a given handle. -/
@[expose]
def getBinding (assignment : Assignment OpInfo) {handleType : HandleType OpInfo}
    (handle : Handle OpInfo handleType) : Option (Binding OpInfo) :=
  assignment.bindings[handle.id]?.join

@[simp]
theorem getBinding_eq_some_iff (assignment : Assignment OpInfo)
    {handleType : HandleType OpInfo} (handle : Handle OpInfo handleType)
    (binding : Binding OpInfo) :
    assignment.getBinding handle = some binding ↔
      assignment.bindings[handle.id]? = some (some binding) := by
  unfold getBinding
  cases assignment.bindings[handle.id]? <;> simp_all

/-- Get the binding for a given operation handle. -/
@[expose]
def getOp (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .op) : Option OperationPtr :=
  match assignment.getBinding handle with
  | some (.op operation) => some operation
  | _ => none

/-- Get the binding for a given value handle. -/
@[expose]
def getValue (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .value) : Option ValuePtr :=
  match assignment.getBinding handle with
  | some (.value value) => some value
  | _ => none

/-- Get the binding for a given type handle. -/
@[expose]
def getType (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .type) : Option TypeAttr :=
  match assignment.getBinding handle with
  | some (.type type) => some type
  | _ => none

/-- Get the binding for a given property handle. -/
@[expose]
def getProperty (assignment : Assignment OpInfo)
    (handle : Handle OpInfo (.prop opCode)) : Option (propertiesOf opCode) :=
  match assignment.getBinding handle with
  | some (.property actualOpCode value) =>
    if h : actualOpCode = opCode then some (h ▸ value) else none
  | _ => none

/-- Get the bindings for an array of type handles. -/
@[expose]
def getTypes (assignment : Assignment OpInfo)
    (types : Array (Handle OpInfo .type)) : Option (Array TypeAttr) :=
  types.mapM (Assignment.getType assignment)

/-- Get the bindings for an array of value handles. -/
@[expose]
def getValues (assignment : Assignment OpInfo)
    (values : Array (Handle OpInfo .value)) : Option (Array ValuePtr) :=
  values.mapM (Assignment.getValue assignment)

/--
Binds a handle. If it is already bound, check that its existing binding agrees, otherwise fail.
-/
@[expose]
def bind (assignment : Assignment OpInfo) {handleType : HandleType OpInfo}
    (handle : Handle OpInfo handleType) (binding : Binding OpInfo) : Option (Assignment OpInfo) :=
  if h : handle.id < assignment.bindings.size then
    match assignment.bindings[handle.id] with
    | none => some ⟨assignment.bindings.set handle.id (some binding)⟩
    | some existing => if existing = binding then some assignment else none
  else
    /- The backing array is extended when the handle is out of bounds. -/
    some ⟨(assignment.bindings ++
      Array.replicate (handle.id - assignment.bindings.size) none).push (some binding)⟩

/-- Bind an operation handle, or check that it already denotes the same operation. -/
@[expose, inline]
def bindOp (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .op) (operation : OperationPtr) : Option (Assignment OpInfo) :=
  Assignment.bind assignment handle (.op operation)

/-- Bind a value handle, or check that it already denotes the same value. -/
@[expose, inline]
def bindValue (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .value) (value : ValuePtr) : Option (Assignment OpInfo) :=
  Assignment.bind assignment handle (.value value)

/-- Bind a type handle, or check that it already denotes the same type. -/
@[expose, inline]
def bindType (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .type) (type : TypeAttr) : Option (Assignment OpInfo) :=
  Assignment.bind assignment handle (.type type)

/-- Bind a property handle, or check that it already denotes the same property. -/
@[expose, inline]
def bindProperty (assignment : Assignment OpInfo)
    (handle : Handle OpInfo (.prop opCode)) (value : propertiesOf opCode) :
    Option (Assignment OpInfo) :=
  Assignment.bind assignment handle (.property opCode value)

/--
Bind a list of value handles to values, or check that it already denotes the same values.
Return `none` if the lists have different lengths.
-/
@[expose, inline, specialize handles]
def bindValues (assignment : Assignment OpInfo)
    (handles : List (Handle OpInfo .value)) (values : List ValuePtr) :
    Option (Assignment OpInfo) :=
  match handles, values with
  | [], [] => some assignment
  | handle :: handles, value :: values => do
    let assignment ← Assignment.bindValue assignment handle value
    Assignment.bindValues assignment handles values
  | _, _ => none

/--
Bind a list of type handles to types, or check that it already denotes the same types.
Return `none` if the lists have different lengths.
-/
@[expose, inline, specialize handles]
def bindTypes (assignment : Assignment OpInfo)
    (handles : List (Handle OpInfo .type)) (types : List TypeAttr) : Option (Assignment OpInfo) :=
  match handles, types with
  | [], [] => some assignment
  | handle :: handles, type :: types => do
    let assignment ← Assignment.bindType assignment handle type
    Assignment.bindTypes assignment handles types
  | _, _ => none

/--
Given a possibly bound operation handle and a list of possibly bound result handles, try to find
the operation that is bound to the operation handle, or that produces one of the bound result
handles.

This function is used during the execution of a `MatchDecl.operation` to find the operation that is
being matched. Since any matched operation should be accessible from the root (either because they
are the root, or because one of their results is used by an operation accessible from the root),
this function should always succeed for any well-formed match program. If it fails, it indicates
that the match program is invalid because the operation is unreachable from the root.
-/
@[expose, inline_if_reduce]
def findOp (assignment : Assignment OpInfo) (opHandle : Handle OpInfo .op)
    (results : Array (Handle OpInfo .value)) : Option OperationPtr :=
  match Assignment.getOp assignment opHandle with
  | some operation => some operation
  | none => do
    let firstBoundResult ← results.findSome? assignment.getValue
    let .opResult resultPtr := firstBoundResult | none
    return resultPtr.op

end Assignment

/--
Interpret a single declarative match instruction, returning `none` if the match fails, or an updated
assignment if it succeeds.
-/
@[expose, inline_if_reduce]
def MatchDecl.run (decl : MatchDecl OpInfo) (ctx : IRContext OpInfo)
    (root : OperationPtr) (assignment : Assignment OpInfo) : Option (Assignment OpInfo) := do
  match decl with
  | .root opHandle =>
    /- A root instruction only binds the root operation to the given handle. -/
    Assignment.bindOp assignment opHandle root
  | .operation opCode operands resultTypes property propertyHandle opHandle results =>
    /- First, find the matched operation through its handle or one of its result handles. -/
    let matchedOp ← Assignment.findOp assignment opHandle results
    /- Then, bind the operation and result handles. -/
    let assignment ← Assignment.bindOp assignment opHandle matchedOp
    let assignment ←
      Assignment.bindValues assignment results.toList (matchedOp.getResults! ctx).toList
    /- Check that the opcode is valid. -/
    guard (matchedOp.getOpType! ctx = opCode)
    let actualProperties := matchedOp.getProperties! ctx opCode
    /- Check that the properties are valid, and bind them. -/
    guard (property actualProperties)
    let assignment ← Assignment.bindProperty assignment propertyHandle actualProperties
    let actualResultTypes := matchedOp.getResultTypes! ctx
    /- Check that the result types are valid and bind them. -/
    guard (actualResultTypes.size = resultTypes.size)
    let assignment ← Assignment.bindTypes assignment
      resultTypes.toList actualResultTypes.toList
    /- Check that the operands are valid and bind them. -/
    let actualOperands := matchedOp.getOperands! ctx
    guard (actualOperands.size = operands.size)
    Assignment.bindValues assignment operands.toList actualOperands.toList
  | .value typeHandle valueHandle =>
    /- Get the value from the assignment (as it should already be bound), and bind its type. -/
    let value ← Assignment.getValue assignment valueHandle
    Assignment.bindType assignment typeHandle (value.getType! ctx)
  | .type matcher typeHandle =>
    /-
    Get the type from the assignment (as it should already be bound), and check that it satisfies
    the matcher.
    -/
    let actual ← Assignment.getType assignment typeHandle
    guard (matcher actual)
    return assignment

/--
Interpret a list of declarative match instructions, returning `none` if any match fails, or an
updated assignment if all matches succeed.
-/
@[expose, inline_if_reduce]
def MatchProg.runDecls (decls : List (MatchDecl OpInfo)) (ctx : IRContext OpInfo)
    (root : OperationPtr) (assignment : Assignment OpInfo) : Option (Assignment OpInfo) :=
  match decls with
  | [] => some assignment
  | decl :: decls => do
    let assignment ← decl.run ctx root assignment
    runDecls decls ctx root assignment

/--
Interpret a match program, returning `none` if any match fails, or an updated assignment if the
match succeeds.
-/
@[expose, inline]
def MatchProg.run (prog : MatchProg OpInfo α) (ctx : IRContext OpInfo)
    (root : OperationPtr) : Option (Assignment OpInfo) :=
  MatchProg.runDecls prog.decls ctx root (Assignment.empty OpInfo prog.numHandles)

/-- Successful matching of `root` by `prog`. -/
@[expose]
def MatchProg.Matches (prog : MatchProg OpInfo α) (ctx : IRContext OpInfo)
    (root : OperationPtr) (assignment : Assignment OpInfo) : Prop :=
  prog.run ctx root = some assignment

/--
Execute one creation declaration, returning any operations it creates and the updated assignment.
-/
@[expose]
def CreateDecl.run (decl : CreateDecl OpInfo) (assignment : Assignment OpInfo)
    (ctx : WfIRContext OpInfo) :
    Option (WfIRContext OpInfo × Array OperationPtr × Assignment OpInfo) := do
  match decl with
  | .property _ value result =>
    let assignment ← Assignment.bindProperty assignment result value
    return (ctx, #[], assignment)
  | .operation opCode operandHandles resultTypeHandles properties opHandle resultHandles =>
    /- Get the operands, result types, and properties of the new operaiton. -/
    let operands ← Assignment.getValues assignment operandHandles
    let resultTypes ← Assignment.getTypes assignment resultTypeHandles
    let properties ← Assignment.getProperty assignment properties
    _root_.guard (resultHandles.size = resultTypes.size)
    if hoper : ∀ operand ∈ operands, operand.InBounds ctx.raw then
      /- Create the new operation and binds it and its results. -/
      let (ctx, newOp) ←
        WfRewriter.createOp ctx opCode resultTypes operands #[] #[] properties none hoper
      let assignment ← Assignment.bindOp assignment opHandle newOp
      let assignment ← Assignment.bindValues assignment resultHandles.toList
        (newOp.getResults! ctx.raw).toList
      return (ctx, #[newOp], assignment)
    else
      none
  | .type value result =>
    let assignment ← Assignment.bindType assignment result value
    return (ctx, #[], assignment)

/--
Execute creation declarations in program order, returning newly created operations as well as the
updated assignment.
-/
@[expose]
def CreateProg.runDecls (decls : List (CreateDecl OpInfo)) (ctx : WfIRContext OpInfo)
    (assignment : Assignment OpInfo) :
    Option (WfIRContext OpInfo × Array OperationPtr × Assignment OpInfo) :=
  match decls with
  | [] => some (ctx, #[], assignment)
  | decl :: decls => do
    let (ctx, newOperations, assignment) ← decl.run assignment ctx
    let (ctx, operations, assignment) ← CreateProg.runDecls decls ctx assignment
    return (ctx, newOperations ++ operations, assignment)

/--
Execute a Puddle creation program. Operations that are created in the process are left uninserted.
-/
@[expose]
def CreateProg.run (prog : CreateProg OpInfo α) (assignment : Assignment OpInfo)
    (ctx : WfIRContext OpInfo) :
    Option (WfIRContext OpInfo × Array OperationPtr × Assignment OpInfo) :=
  CreateProg.runDecls prog.decls ctx assignment

/-- Interpret a Puddle pattern.

Matcher rejection returns a nonfatal no-match result. After matching succeeds, any failure
is a fatal rewrite error. -/
@[expose, specialize rule]
def Pattern.interpret (rule : Pattern OpInfo) : LocalRewritePattern OpInfo :=
  fun ctx root =>
    /- First, run the matcher. -/
    match rule.matcher.run ctx.raw root with
    | none => some (ctx, none)
    | some assignment =>
      /- If it succeeds, create the new operations. -/
      match rule.creation.run assignment ctx with
      | none => none
      | some (newCtx, newOps, assignment) =>
        /- Finally, extract the replacement values. -/
        match assignment.getValues rule.replacement.values with
        | none => none
        | some newValues => some (newCtx, some (newOps, newValues))

/--
A compiled Puddle pattern stored as data rather than exposed directly as a function-valued
definition. Closed values of this type can be initialized once and their rewrite closure reused
for every operation visited by a rewrite driver.
-/
structure CompiledPattern (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The reusable pattern-rewriter entry point. -/
  run : RewritePattern OpInfo

/--
Compile a Puddle rule into a reusable rewrite-pattern value.
This function is more efficient than `Pattern.interpret` because it allows the Lean compiler to
initialize things only once, rather than reinitializing them for each application of the pattern.
-/
@[expose, specialize rule]
def Pattern.compile (rule : Pattern OpInfo) : CompiledPattern OpInfo :=
  ⟨RewritePattern.fromLocalRewrite (Pattern.interpret rule)⟩

end

end Veir.Puddle
