module

public import Veir.PatternRewriter.Puddle.Metadata
public import Veir.PatternRewriter.Basic

import all Veir.IR.Basic

/-!
# Execution of a Puddle pattern

This file defines the necessary functions to execute a Puddle pattern on a given operation.
It currently only supports matching a pattern against a root operation, and does not support
creating or replacing operations.
-/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Assignment and Bindings

This section defines the runtime representation of a Puddle pattern match, which consists of an
assignment of handles (`Assignment`) to concrete IR entities (`Binding`).
-/

/-- Runtime values bound by Puddle handles. -/
inductive Binding (OpInfo : Type) [HasOpInfo OpInfo] where
| op (operation : OperationPtr)
| value (value : ValuePtr)
| type (type : TypeAttr)
| property (opCode : OpInfo) (value : propertiesOf opCode)
deriving DecidableEq

/-- Runtime bindings associating handles (with their IDs) to concrete IR entities. -/
structure Assignment (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- Slots allocated by the matcher and extended as creation introduces new handles. -/
  bindings : Array (Option (Binding OpInfo))

namespace Assignment

/-- An empty assignment with the specified number of slots for handles. -/
@[expose]
def empty (OpInfo : Type) [HasOpInfo OpInfo] (size : Nat) : Assignment OpInfo :=
  ⟨Array.replicate size none⟩

/-- Read a binding, treating an unused slot and an out-of-bounds index identically. -/
@[expose]
def getBinding (assignment : Assignment OpInfo) (id : Nat) : Option (Binding OpInfo) :=
  assignment.bindings[id]?.join

@[simp]
theorem getBinding_eq_some_iff (assignment : Assignment OpInfo) (id : Nat)
    (binding : Binding OpInfo) :
    assignment.getBinding id = some binding ↔
      assignment.bindings[id]? = some (some binding) := by
  unfold getBinding
  cases assignment.bindings[id]? <;> simp_all

@[expose]
def getOp (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .op) : Option OperationPtr :=
  match assignment.getBinding handle.id with
  | some (.op operation) => some operation
  | _ => none

@[expose]
def getValue (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .value) : Option ValuePtr :=
  match assignment.getBinding handle.id with
  | some (.value value) => some value
  | _ => none

@[expose]
def getType (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .type) : Option TypeAttr :=
  match assignment.getBinding handle.id with
  | some (.type type) => some type
  | _ => none

@[expose]
def getProperty (assignment : Assignment OpInfo)
    (handle : Handle OpInfo (.prop opCode)) : Option (propertiesOf opCode) :=
  match assignment.getBinding handle.id with
  | some (.property actualOpCode value) =>
    if h : actualOpCode = opCode then some (h ▸ value) else none
  | _ => none

@[expose]
def getTypes (assignment : Assignment OpInfo)
    (types : Array (Handle OpInfo .type)) : Option (Array TypeAttr) :=
  types.mapM (Assignment.getType assignment)

/-- Resolve a list of matched or created value handles. -/
@[expose]
def getValues (assignment : Assignment OpInfo)
    (values : Array (Handle OpInfo .value)) : Option (Array ValuePtr) :=
  values.mapM (Assignment.getValue assignment)

@[expose]
def bind (assignment : Assignment OpInfo)
    (id : Nat) (binding : Binding OpInfo) : Assignment OpInfo :=
  if h : id < assignment.bindings.size then
    ⟨assignment.bindings.set id (some binding)⟩
  else
    ⟨assignment.bindings ++ Array.replicate (id - assignment.bindings.size) none ++
      #[some binding]⟩

@[expose, inline]
def bindOp (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .op) (operation : OperationPtr) : Assignment OpInfo :=
  Assignment.bind assignment handle.id (.op operation)

@[expose, inline]
def bindValue (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .value) (value : ValuePtr) : Assignment OpInfo :=
  Assignment.bind assignment handle.id (.value value)

@[expose, inline]
def bindType (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .type) (type : TypeAttr) : Assignment OpInfo :=
  Assignment.bind assignment handle.id (.type type)

@[expose, inline]
def bindProperty (assignment : Assignment OpInfo)
    (handle : Handle OpInfo (.prop opCode)) (value : propertiesOf opCode) : Assignment OpInfo :=
  Assignment.bind assignment handle.id (.property opCode value)

instance : MetadataStore OpInfo (Assignment OpInfo) where
  getType := Assignment.getType
  getProperty := fun store {_opCode} handle => Assignment.getProperty store handle
  bindType store handle value := some (Assignment.bindType store handle value)
  bindProperty := fun store {_opCode} handle value =>
    some (Assignment.bindProperty store handle value)

@[expose, inline, specialize handles]
def bindValues (assignment : Assignment OpInfo)
    (handles : List (Handle OpInfo .value)) (values : List ValuePtr) :
    Assignment OpInfo :=
  match handles, values with
  | handle :: handles, value :: values =>
    Assignment.bindValues
      (Assignment.bindValue assignment handle value) handles values
  | _, _ => assignment

@[expose]
def matchBind (assignment : Assignment OpInfo)
    (id : Nat) (binding : Binding OpInfo) : Option (Assignment OpInfo) :=
  if h : id < assignment.bindings.size then
    match assignment.bindings[id] with
    | none => some ⟨assignment.bindings.set id (some binding)⟩
    | some existing => if existing = binding then some assignment else none
  else
    none

@[expose, inline]
def matchBindOp (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .op) (operation : OperationPtr) : Option (Assignment OpInfo) :=
  Assignment.matchBind assignment handle.id (.op operation)

@[expose]
def matchBindType (assignment : Assignment OpInfo)
    (handle : Handle OpInfo .type) (type : TypeAttr) : Option (Assignment OpInfo) :=
  Assignment.matchBind assignment handle.id (.type type)

@[expose]
def matchBindProperty (assignment : Assignment OpInfo)
    (handle : Handle OpInfo (.prop opCode)) (value : propertiesOf opCode) : Option (Assignment OpInfo) :=
  Assignment.matchBind assignment handle.id (.property opCode value)

/-- Metadata access for the matching phase, which only binds preallocated matcher slots. -/
@[expose]
def matchMetadataStore : MetadataStore OpInfo (Assignment OpInfo) where
  getType := Assignment.getType
  getProperty := fun store {_opCode} handle => Assignment.getProperty store handle
  bindType := Assignment.matchBindType
  bindProperty := fun store {_opCode} handle value =>
    Assignment.matchBindProperty store handle value

@[expose]
def matchBindValue (assignment : Assignment OpInfo)
    (pattern : Handle OpInfo .value) (value : ValuePtr) : Option (Assignment OpInfo) :=
  Assignment.matchBind assignment pattern.id (.value value)

@[expose, inline, specialize patterns]
def matchBindValues (assignment : Assignment OpInfo)
    (patterns : List (Handle OpInfo .value)) (values : List ValuePtr) :
    Option (Assignment OpInfo) :=
  match patterns, values with
  | [], [] => some assignment
  | pattern :: patterns, value :: values => do
    let assignment ← Assignment.matchBindValue assignment pattern value
    Assignment.matchBindValues assignment patterns values
  | _, _ => none

@[expose, inline, specialize handles]
def matchBindTypes (assignment : Assignment OpInfo)
    (handles : List (Handle OpInfo .type)) (types : List TypeAttr) : Option (Assignment OpInfo) :=
  match handles, types with
  | [], [] => some assignment
  | handle :: handles, type :: types => do
    let assignment ← Assignment.matchBindType assignment handle type
    Assignment.matchBindTypes assignment handles types
  | _, _ => none

@[expose, inline_if_reduce]
def matchGetOrBindOp (assignment : Assignment OpInfo)
    (_ctx : IRContext OpInfo) (opHandle : Handle OpInfo .op)
    (results : Array (Handle OpInfo .value)) : Option (OperationPtr × Assignment OpInfo) :=
  match Assignment.getOp assignment opHandle with
  | some concrete => some (concrete, assignment)
  | none => do
    let resultHandle ← results[0]?
    let value ← Assignment.getValue assignment resultHandle
    let .opResult resultPtr := value | none
    if resultPtr.index = 0 then
      let definingOp := resultPtr.op
      let assignment ← Assignment.matchBindOp assignment opHandle definingOp
      return (definingOp, assignment)
    else none

@[expose, inline_if_reduce]
def matchCheckOperationResult (assignment : Assignment OpInfo)
    (operation : OperationPtr) (results : Array (Handle OpInfo .value)) : Option Unit :=
  match results[0]? with
  | none => some ()
  | some resultHandle => do
    let value ← Assignment.getValue assignment resultHandle
    _root_.guard (value = .opResult (operation.getResult 0))

end Assignment

/-- Resolve a creation operand against the rule-wide assignment. -/
@[expose]
def CreateOperand.resolveValue (operand : CreateOperand OpInfo)
    (assignment : Assignment OpInfo) : Option ValuePtr :=
  Assignment.getValue assignment operand.value

@[expose]
def CreateOperand.resolveValues (operands : Array (CreateOperand OpInfo))
    (assignment : Assignment OpInfo) : Option (Array ValuePtr) :=
  operands.mapM fun operand => operand.resolveValue assignment

@[expose, inline_if_reduce]
def MatchDecl.match (decl : MatchDecl OpInfo) (ctx : IRContext OpInfo)
    (root : OperationPtr) (assignment : Assignment OpInfo) : Option (Assignment OpInfo) := do
  match decl with
  | .root _ _ _ _ _ opHandle =>
    Assignment.matchBindOp assignment opHandle root
  | .operation opCode operands returnTypes property propertyHandle opHandle results =>
    let (concrete, assignment) ← Assignment.matchGetOrBindOp assignment ctx opHandle results
    let _ ← Assignment.matchCheckOperationResult assignment concrete results
    _root_.guard (concrete.getOpType! ctx = opCode)
    let actualProperties := concrete.getProperties! ctx opCode
    _root_.guard (property actualProperties)
    let assignment ← Assignment.matchBindProperty assignment propertyHandle actualProperties
    let actualReturnTypes := concrete.getResultTypes! ctx
    _root_.guard (actualReturnTypes.size = returnTypes.size)
    let assignment ← Assignment.matchBindTypes assignment
      returnTypes.toList actualReturnTypes.toList
    let actualOperands := concrete.getOperands! ctx
    _root_.guard (actualOperands.size = operands.size)
    Assignment.matchBindValues assignment operands.toList actualOperands.toList
  | .value typeHandle valueHandle =>
    let value ← Assignment.getValue assignment valueHandle
    Assignment.matchBindType assignment typeHandle (value.getType! ctx)
  | .type matcher typeHandle =>
    let actual ← Assignment.getType assignment typeHandle
    _root_.guard (matcher actual)
    return assignment
  | @MatchDecl.guard _ _ Inputs inputBundle inputs predicate =>
    let values ← @MetadataTuple.resolve OpInfo _ Inputs (Assignment OpInfo) inputBundle
      Assignment.matchMetadataStore assignment inputs
    _root_.guard (predicate values)
    return assignment

@[expose, inline_if_reduce]
def MatchProg.matchDecls (decls : List (MatchDecl OpInfo)) (ctx : IRContext OpInfo)
    (root : OperationPtr) (assignment : Assignment OpInfo) : Option (Assignment OpInfo) :=
  match decls with
  | [] => some assignment
  | decl :: decls => do
    let assignment ← decl.match ctx root assignment
    matchDecls decls ctx root assignment

/-- Interpret a declarative pattern backwards from the distinguished root. -/
@[expose, inline]
def MatchProg.run (prog : MatchProg OpInfo α) (ctx : IRContext OpInfo)
    (root : OperationPtr) : Option (Assignment OpInfo) :=
  MatchProg.matchDecls prog.decls ctx root (Assignment.empty OpInfo prog.numHandles)

/-- Successful matching is the hypothesis consumed by later rule-validity proofs. -/
@[expose]
def MatchProg.Matches (prog : MatchProg OpInfo α) (ctx : IRContext OpInfo)
    (root : OperationPtr) (assignment : Assignment OpInfo) : Prop :=
  prog.run ctx root = some assignment

/-- Resolve the values selected by a terminal replacement. -/
@[expose]
def Replacement.resolveValues (replacement : Replacement OpInfo)
    (assignment : Assignment OpInfo) : Option (Array ValuePtr) :=
  Assignment.getValues assignment replacement

/-- Resolve a terminal replacement.

The replacement must provide one value for every root result, and never permits a root result to
replace the root itself. -/
@[expose]
def Replacement.resolve (replacement : Replacement OpInfo) (assignment : Assignment OpInfo)
    (ctx : IRContext OpInfo)
  (root : OperationPtr) : Option (Array ValuePtr) := do
  let values ← replacement.resolveValues assignment
  _root_.guard (root.getNumResults! ctx = values.size)
  _root_.guard (∀ value ∈ values, value ∉ root.getResults! ctx)
  return values

/-- Resolve a literal or handle-sourced property record. -/
@[expose]
def CreateProperty.resolve (property : CreateProperty OpInfo opCode)
    (assignment : Assignment OpInfo) : Option (propertiesOf opCode) :=
  match property with
  | CreateProperty.literal value => some value
  | CreateProperty.handle propertyHandle => Assignment.getProperty assignment propertyHandle

/-- Execute one creation declaration and bind its operation and result handles. -/
@[expose]
def CreateDecl.run (decl : CreateDecl OpInfo) (assignment : Assignment OpInfo)
    (ctx : WfIRContext OpInfo) :
    Option (WfIRContext OpInfo × Assignment OpInfo × OperationPtr) := do
  match decl with
  | .operation opCode operandHandles resultTypeHandles properties opHandle resultHandles =>
    let operands ← CreateOperand.resolveValues operandHandles assignment
    let resultTypes ← Assignment.getTypes assignment resultTypeHandles
    let properties ← properties.resolve assignment
    let returnValue ← operands[0]?
    let returnType ← resultTypes[0]?
    _root_.guard (resultTypes.size = 1)
    _root_.guard (resultHandles.size = resultTypes.size)
    _root_.guard (returnType = returnValue.getType! ctx.raw)
    if hoper : ∀ operand ∈ operands, operand.InBounds ctx.raw then
      let (ctx, newOp) ←
        WfRewriter.createOp ctx opCode resultTypes operands #[] #[] properties none hoper
      let assignment := Assignment.bindOp assignment opHandle newOp
      let assignment := Assignment.bindValues assignment resultHandles.toList
        (newOp.getResults! ctx.raw).toList
      return (ctx, assignment, newOp)
    else
      none
  | @CreateDecl.applyNative _ _ _ _ _ _ _ _ _ => none

/-- Execute creation declarations in program order, returning operations in that same order. -/
@[expose]
def CreateProg.runDecls (decls : List (CreateDecl OpInfo)) (ctx : WfIRContext OpInfo)
    (assignment : Assignment OpInfo) :
    Option (WfIRContext OpInfo × Array OperationPtr × Assignment OpInfo) :=
  match decls with
  | [] => some (ctx, #[], assignment)
  | (@CreateDecl.applyNative _ _ _ _ inputBundle outputBundle
      inputs rewrite outputs) :: decls => do
    let values ← MetadataTuple.resolve (self := inputBundle) assignment inputs
    let outputValues ← rewrite values
    let assignment ← MetadataTuple.bind (self := outputBundle) assignment outputs outputValues
    CreateProg.runDecls decls ctx assignment
  | decl :: decls => do
    let (ctx, assignment, operation) ← decl.run assignment ctx
    let (ctx, operations, assignment) ← CreateProg.runDecls decls ctx assignment
    return (ctx, #[operation] ++ operations, assignment)

/-- Execute an ordered creation program. Operations are left uninserted for the rewrite driver. -/
@[expose]
def CreateProg.run (prog : CreateProg OpInfo α) (assignment : Assignment OpInfo)
    (ctx : WfIRContext OpInfo) :
    Option (WfIRContext OpInfo × Array OperationPtr × Assignment OpInfo) :=
  CreateProg.runDecls prog.decls ctx assignment

/-- Compile a Puddle rule to the local rewrite-pattern interface.

Matcher rejection returns a nonfatal no-match result. After matching succeeds, failure in native
metadata evaluation, operation creation, or replacement resolution is a fatal rewrite error. -/
@[expose, specialize rule]
def Pattern.compile (rule : Pattern OpInfo) : LocalRewritePattern OpInfo :=
  fun ctx root =>
    match rule.matcher.run ctx.raw root with
    | none => some (ctx, none)
    | some assignment =>
      match rule.creation.run assignment ctx with
      | none => none
      | some (newCtx, newOps, assignment) =>
        match rule.replacement.resolve assignment newCtx.raw root with
        | none => none
        | some newValues => some (newCtx, some (newOps, newValues))

end

end Veir.Puddle
