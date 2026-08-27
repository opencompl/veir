module

public import Veir.PatternRewriter.Puddle.Definitions

/-!
# Puddle Patterns Validity

This file defines the obligations for a Puddle pattern to be considered valid (`Pattern.Valid`),
both structurally and semantically. If `Pattern.Valid` holds, then compiling the Puddle pattern to
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Supported Opcodes

Puddle currently supports operations that cannot terminate a block and have no memory effects.
-/

/--
An opcode is supported when it is not a terminator and has no memory effects for any possible
property value.

We could in the future support opcodes when we know that the properties matched or created by the
pattern are such that the operation has no memory effects, but this is only happening in rare cases.
-/
def SupportedOpCode (opCode : OpInfo) : Prop :=
  HasOpInfo.isTerminator opCode = false ∧
    ∀ property, HasOpInfo.getEffects opCode property = .none

/-- A match declaration is supported when the opcode of an operation declaration is supported. -/
@[expose]
def MatchDecl.Supported (decl : MatchDecl OpInfo) : Prop :=
  match decl with
  | .operation opCode _ _ _ _ _ _ _ => SupportedOpCode opCode
  | _ => True

/-- Every declaration in a match program uses supported opcodes. -/
@[expose]
def MatchProg.Supported (prog : MatchProg OpInfo α) : Prop :=
  (∀ decl ∈ prog.decls, decl.Supported)

/-- A creation declaration is supported when the opcode of an operation declaration is supported. -/
@[expose]
def CreateDecl.Supported : CreateDecl OpInfo → Prop
  | .operation opCode _ _ _ _ _ => SupportedOpCode opCode
  | _ => True

/-- Every declaration in a creation program uses supported opcodes. -/
@[expose]
def CreateProg.Supported (prog : CreateProg OpInfo α) : Prop :=
  ∀ decl ∈ prog.decls, decl.Supported

/-- The pattern only references supported opcodes. -/
@[expose]
def Pattern.Supported (rule : Pattern OpInfo) : Prop :=
  rule.matcher.Supported ∧ rule.creation.Supported

/-! ## Root Constraint -/

/--
The first declaration in the match program is an operation declaration whose operation handle is
the program's distinguished root handle.
-/
def MatchProg.ConstrainsRoot (prog : MatchProg OpInfo α) : Prop :=
  match prog.decls with
  | .operation _ _ _ _ _ opHandle _ _ :: _ => opHandle = prog.rootHandle
  | _ => False

/-- Return the hidden SSA-result handles from the program's leading root constraint. -/
@[expose]
def MatchProg.rootResults? (prog : MatchProg OpCode α) :
    Option (Array (Handle OpCode .value)) :=
  match prog.decls with
  | .operation _ _ _ _ _ opHandle results _ :: _ =>
    if opHandle = prog.rootHandle then some results else none
  | _ => none

/-! ## Structural well-formedness -/

/-- The abstract context of handle identifiers and their runtime kinds. -/
structure HandleContext where
  bindings : List (Nat × HandleType OpCode)
  unavailable : List Nat
deriving DecidableEq

namespace HandleContext

/-- The empty handle context. -/
def empty : HandleContext := ⟨[], []⟩

/-- Look up the kind occupying an identifier. -/
def lookup (handles : HandleContext) (id : Nat) : Option (HandleType OpCode) :=
  let rec lookupBindings : List (Nat × HandleType OpCode) → Option (HandleType OpCode)
    | [] => none
    | (definedId, kind) :: rest =>
        if definedId = id then some kind else lookupBindings rest
  lookupBindings handles.bindings

/-- Succeed exactly when a typed handle has already been defined with precisely that kind. -/
@[expose]
def require (handles : HandleContext) {kind : HandleType OpCode}
    (handle : Handle OpCode kind) : Option HandleContext :=
  if handles.lookup handle.id = some kind ∧ handle.id ∉ handles.unavailable then
    some handles
  else
    none

/--
Record a matcher-defined handle. Repeated definitions of the same typed handle are permitted,
because matcher binding is idempotent, but reusing an identifier at another kind is rejected.
-/
def insert (handles : HandleContext) {kind : HandleType OpCode}
    (handle : Handle OpCode kind) : Option HandleContext :=
  match handles.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: handles.bindings, handles.unavailable⟩
  | some actual => if actual = kind then some handles else none

/-- Record several matcher-defined handles. -/
@[expose]
def insertMany (handles : HandleContext) :
    List (Handle OpCode kind) → Option HandleContext
  | [] => some handles
  | handle :: rest => do
      let handles ← handles.insert handle
      handles.insertMany rest

/--
Record a creation output, requiring its identifier to be entirely fresh regardless of kind.
-/
def insertFresh (handles : HandleContext) {kind : HandleType OpCode}
    (handle : Handle OpCode kind) : Option HandleContext :=
  match handles.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: handles.bindings, handles.unavailable⟩
  | some _ => none

/-- Record several creation outputs, checking freshness between the outputs as well. -/
@[expose]
def insertManyFresh (handles : HandleContext) :
    List (Handle OpCode kind) → Option HandleContext
  | [] => some handles
  | handle :: rest => do
      let handles ← handles.insertFresh handle
      handles.insertManyFresh rest

/-- Require every handle in a homogeneous list to be available. -/
@[expose]
def requireMany (handles : HandleContext) :
    List (Handle OpCode kind) → Option HandleContext
  | [] => some handles
  | handle :: used => do
      let handles ← handles.require handle
      handles.requireMany used

/-- Mark an allocated handle as unavailable to creation and replacement inputs. -/
def forbid (handles : HandleContext) (handle : Handle OpCode kind) : HandleContext :=
  ⟨handles.bindings, handle.id :: handles.unavailable⟩

/-- Mark several allocated handles as unavailable while retaining them for freshness checks. -/
@[expose]
def forbidMany (handles : HandleContext) :
    List (Handle OpCode kind) → HandleContext
  | [] => handles
  | handle :: rest => (handles.forbid handle).forbidMany rest

end HandleContext

/-- Collect the handles that a matcher declaration can bind during a successful match. -/
@[expose]
def MatchDecl.collectBindings (decl : MatchDecl OpCode)
    (defined : HandleContext) : Option HandleContext := do
  match decl with
  | .operation _ operands resultTypes _ propertyHandle opHandle results _ =>
      let defined ← defined.insert opHandle
      let defined ← defined.insertMany results.toList
      let defined ← defined.insert propertyHandle
      let defined ← defined.insertMany resultTypes.toList
      defined.insertMany operands.toList
  | .value typeHandle _ =>
      defined.insert typeHandle
  | .type .. =>
      some defined

/-- Collect matcher-defined handles globally, without imposing matcher use-point ordering. -/
@[expose]
def MatchProg.collectBindingsDecls :
    List (MatchDecl OpCode) → HandleContext → Option HandleContext
  | [], defined => some defined
  | decl :: decls, defined => do
      let defined ← decl.collectBindings defined
      MatchProg.collectBindingsDecls decls defined

/-- Collect every handle that can be bound by a successful matcher. -/
@[expose]
def MatchProg.collectBindings (prog : MatchProg OpCode α) : Option HandleContext :=
  do
    let rootResults ← prog.rootResults?
    let defined ← HandleContext.empty.insert prog.rootHandle
    let defined ← MatchProg.collectBindingsDecls prog.decls defined
    let defined := defined.forbid prog.rootHandle
    return defined.forbidMany rootResults.toList

/--
Check one creation declaration and extend the context with its outputs. Inputs must be available at
this exact program point, while all outputs must have globally fresh identifiers.
-/
@[expose]
def CreateDecl.checkBindings (decl : CreateDecl OpCode)
    (defined : HandleContext) : Option HandleContext := do
  match decl with
  | .type _ result =>
      defined.insertFresh result
  | .property _ _ result =>
      defined.insertFresh result
  | .operation _ operands resultTypes properties opHandle resultHandles =>
      let defined ← defined.requireMany operands.toList
      let defined ← defined.requireMany resultTypes.toList
      let defined ← defined.require properties
      guard (resultHandles.size = resultTypes.size)
      let defined ← defined.insertFresh opHandle
      defined.insertManyFresh resultHandles.toList

/-- Traverse creation declarations in execution order, threading the available-handle context. -/
@[expose]
def CreateProg.checkBindingsDecls :
    List (CreateDecl OpCode) → HandleContext → Option HandleContext
  | [], defined => some defined
  | decl :: decls, defined => do
      let defined ← decl.checkBindings defined
      CreateProg.checkBindingsDecls decls defined

/-- Validate a creation program from a matcher-defined handle context. -/
@[expose]
def CreateProg.checkBindings (prog : CreateProg OpCode α)
    (defined : HandleContext) : Option HandleContext :=
  CreateProg.checkBindingsDecls prog.decls defined

/-- Require every replacement value to be available after the creation program. -/
@[expose]
def Replacement.checkBindings (replacement : Replacement OpCode)
    (defined : HandleContext) : Option HandleContext :=
  defined.requireMany replacement.values.toList

/-- Run the complete structural checker. -/
@[expose]
def Pattern.checkStructure (rule : Pattern OpCode) : Option HandleContext := do
  let defined ← rule.matcher.collectBindings
  let defined ← rule.creation.checkBindings defined
  rule.replacement.checkBindings defined

/--
Structural validity for the whole rule. The matcher is collected globally; creation is checked in
execution order; replacement is checked against the final context.
-/
@[expose]
def Pattern.StructurallyWellFormed (rule : Pattern OpCode) : Prop :=
  rule.checkStructure.isSome = true

instance (rule : Pattern OpCode) : Decidable rule.StructurallyWellFormed := by
  unfold Pattern.StructurallyWellFormed
  infer_instance

/-!
## Pattern Validity

`Pattern.Valid` is the predicate that a Puddle pattern is both sound structurally and
semantically.  If `Pattern.Valid` holds, then compiling the Puddle pattern to
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

/-- The static validity conditions required by a Puddle pattern. -/
structure Pattern.Valid (rule : Pattern OpCode) : Prop where
  /-- Every operation declaration in the pattern uses a supported opcode. -/
  Supported : rule.Supported
  /-- The match program starts with an operation declaration constraining its root handle. -/
  ConstrainsRoot : rule.matcher.ConstrainsRoot
  structurallyWellFormed : rule.StructurallyWellFormed
end

end Veir.Puddle
