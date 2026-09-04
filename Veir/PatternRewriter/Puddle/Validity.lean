module

public import Veir.PatternRewriter.Puddle.Builders

/-!
# Puddle Patterns Validity

This file defines the obligations for a Puddle pattern to be considered valid (`Pattern.Valid`),
both structurally and semantically. If `Pattern.Valid` holds, then compiling the Puddle pattern
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Supported Opcodes

Puddle currently only supports operations that cannot terminate a block and have no memory effects.
-/

/--
An opcode is supported when it is not a terminator and has no memory effects for any possible
property value.

We could in the future support opcodes when we know that the properties matched or created by the
pattern are such that the operation has no memory effects, but this is only happening in rare cases.
-/
@[expose]
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
  ∀ decl ∈ prog.decls, decl.Supported

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
@[expose]
def MatchProg.ConstrainsRoot (prog : MatchProg OpInfo α) : Prop :=
  match prog.decls with
  | .operation _ _ _ _ _ opHandle _ _ :: _ => opHandle = prog.rootHandle
  | _ => False

/--
Return the hidden SSA-result handles from the program's root constraint.

The root is assumed to be the first declaration in the match program. If it is not, then this
function returns `none`.
-/
@[expose]
def MatchProg.rootResults? (prog : MatchProg OpCode α) :
    Option (Array (Handle OpCode .value)) :=
  match prog.decls with
  | .operation _ _ _ _ _ opHandle results _ :: _ =>
    if opHandle = prog.rootHandle then some results else none
  | _ => none

/-!
## Structural well-formedness

This section defines `Pattern.StructurallyWellFormed`, the obligations of a Puddle pattern to be
considered structurally well-formed, and therefore structurally valid. While `Builders` ensure that
the pattern is well-formed, it is still possible to construct a pattern that is not well-formed by
using the underlying `MatchProg` and `CreateProg` constructors directly.
-/

/--
The abstract context of handle identifiers and their runtime kinds.

This context is used to record the handles that have been bound by the matcher and creation phase,
to check at each step if the inputs are available, and if the output is fresh, or was declared with
the same kind.
-/
structure HandleContext where
  /- The bindings ids that have been established, with their kinds. -/
  bindings : List (Nat × HandleType OpCode)
  /-
  The bindings that have been established, but that are not allowed to be used.
  This is used to mark the root and its results as unavailable to the creation phase and
  replacement phase, even though they are still bound by the matcher.
  -/
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
def require (ctx : HandleContext) (handle : Handle OpCode kind) : Bool :=
  ctx.lookup handle.id = some kind ∧ handle.id ∉ ctx.unavailable

/-- Require every handle in a homogeneous list to be available. -/
@[expose]
def requireMany (ctx : HandleContext) (handles : List (Handle OpCode kind)) : Bool :=
  handles.all ctx.require

/--
Record a matcher-defined handle. Repeated definitions of the same typed handle are permitted,
but reusing an identifier at another kind is rejected.
-/
def insert (ctx : HandleContext) (handle : Handle OpCode kind) : Option HandleContext :=
  match ctx.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: ctx.bindings, ctx.unavailable⟩
  | some actual => if actual = kind then some ctx else none

/-- Record several matcher-defined handles. -/
@[expose]
def insertMany (ctx : HandleContext) (handles : List (Handle OpCode kind))
    : Option HandleContext :=
  handles.foldlM insert ctx

/-- Record a creation output, requiring its identifier to be fresh in the context. -/
def insertFresh (ctx : HandleContext) (handle : Handle OpCode kind) : Option HandleContext :=
  match ctx.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: ctx.bindings, ctx.unavailable⟩
  | some _ => none

/-- Record several creation outputs, checking freshness between the outputs as well. -/
@[expose]
def insertManyFresh (ctx : HandleContext) (handles : List (Handle OpCode kind))
    : Option HandleContext :=
  handles.foldlM insertFresh ctx

/-- Mark an allocated handle as unavailable to creation and replacement inputs. -/
def forbid (ctx : HandleContext) (handle : Handle OpCode kind) : HandleContext :=
  ⟨ctx.bindings, handle.id :: ctx.unavailable⟩

/-- Mark several allocated handles as unavailable while retaining them for freshness checks. -/
@[expose]
def forbidMany (ctx : HandleContext) (handles : List (Handle OpCode kind)) : HandleContext :=
  handles.foldl forbid ctx

end HandleContext

/-- Collect the handles that a matcher declaration binds during a successful match. -/
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
  | .type _ _ =>
      some defined

/--
Collect all the handles that a list of matcher declarations bind during a successful match.
In particular, this includes the root result handles.
-/
@[expose]
def MatchProg.collectDeclBindings :
    List (MatchDecl OpCode) → HandleContext → Option HandleContext
  | [], defined => some defined
  | decl :: decls, defined => do
      let defined ← decl.collectBindings defined
      MatchProg.collectDeclBindings decls defined

/--
Collect every available handle that can be bound by a successful matcher, and mark as unavailable
the root operation handle and its result handles.
-/
@[expose]
def MatchProg.collectBindings (prog : MatchProg OpCode α) : Option HandleContext :=
  do
    let rootResults ← prog.rootResults?
    let defined ← HandleContext.empty.insert prog.rootHandle
    let defined ← MatchProg.collectDeclBindings prog.decls defined
    let defined := defined.forbid prog.rootHandle
    return defined.forbidMany rootResults.toList

/--
Check one creation declaration and extend the context with its outputs. Inputs must be available at
this exact program point, while all outputs must have globally fresh identifiers.
-/
@[expose]
def CreateDecl.checkBindings (ctx : HandleContext) (decl : CreateDecl OpCode)
    : Option HandleContext := do
  match decl with
  | .type _ result =>
      ctx.insertFresh result
  | .property _ _ result =>
      ctx.insertFresh result
  | .operation _ operands resultTypes properties opHandle resultHandles =>
      guard (ctx.requireMany operands.toList)
      guard (ctx.requireMany resultTypes.toList)
      guard (ctx.require properties)
      guard (resultHandles.size = resultTypes.size)
      let defined ← ctx.insertFresh opHandle
      defined.insertManyFresh resultHandles.toList

/-- Validate a creation program from a matcher-defined handle context. -/
@[expose]
def CreateProg.checkBindings (ctx : HandleContext) (prog : CreateProg OpCode α)
    : Option HandleContext :=
  prog.decls.foldlM CreateDecl.checkBindings ctx

/-- Require every replacement value to be available after the creation program. -/
@[expose]
def Replacement.checkBindings (replacement : Replacement OpCode)
    (ctx : HandleContext) : Bool :=
  ctx.requireMany replacement.values.toList

/-- Run the complete structural checker on a pattern. -/
@[expose]
def Pattern.checkStructure (rule : Pattern OpCode) : Option HandleContext := do
  let defined ← rule.matcher.collectBindings
  let defined ← rule.creation.checkBindings defined
  guard (rule.replacement.checkBindings defined)
  return defined

/--
Structural validity of a Puddle pattern. It checks that:
* the match program begins with an operation declaration for its root;
* matcher bindings that share an identifier also share a runtime kind;
* every creation input is bound by the matcher or by an earlier creation declaration;
* every creation output has an identifier that is globally fresh;
* each created operation has as many result handles as result-type handles;
* every replacement value is bound by the matcher or the creation program; and
* the matched root and its results are not available to the creation or replacement phases.
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
semantically.  If `Pattern.Valid` holds, then compiling the Puddle pattern
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

/-- The static validity conditions required by a Puddle pattern. -/
structure Pattern.Valid (rule : Pattern OpCode) : Prop where
  /-- Every operation declaration in the pattern uses a supported opcode. -/
  Supported : rule.Supported
  /-- The match program starts with an operation declaration constraining its root handle. -/
  ConstrainsRoot : rule.matcher.ConstrainsRoot
  /-- Structural validity of the pattern. -/
  structurallyWellFormed : rule.StructurallyWellFormed
end

/-!
## Validity Tactics

This section defines tactics for proving the different obligations of `Pattern.Valid`. These tactics
are intended to be used in the proof of `Pattern.Valid` for a specific Puddle pattern.
-/

/-- Unfold and simplify the builders used to construct a concrete Puddle pattern. -/
macro "unfoldPuddleBuilder" : tactic =>
  `(tactic| (
    /- Unfold the builder functions -/
    simp only [Pattern.Builder, MatchProg.build, CreateProg.build, bind, pure,
      MatchProg.value, MatchProg.type, MatchProg.root, MatchProg.operation, CreateProg.operation,
      CreateProg.property];
    /- Simplify the resulting expressions with standard simplifications -/
    simp only [Nat.zero_add, Nat.reduceAdd, List.size_toArray, List.length_cons, List.length_nil,
      Array.size_map, Array.size_range, Nat.lt_add_one, getElem!_pos, Array.getElem_map,
      Array.getElem_range, Nat.add_zero, List.cons_append, List.nil_append, List.reverse_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]))

/-- Prove a `Puddle.Supported` goal. -/
macro "provePuddleSupported" : tactic =>
  `(tactic| (
    simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator];
    done
  ))

/-- Prove a `Puddle.Valid` goal. -/
macro "provePuddleValid" : tactic =>
  `(tactic| (
    unfoldPuddleBuilder
    constructor
    · provePuddleSupported
    · cbv
    · cbv
  ))

end Veir.Puddle
