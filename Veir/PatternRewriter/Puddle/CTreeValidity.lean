module

public import Veir.PatternRewriter.Puddle.Builders
public import Veir.Interpreter.Refinement.Lemmas
public import Veir.PatternRewriter.Puddle.Validity
public import Veir.Interpreter.CTreeInterpreter
public import Veir.Dialects.Arith.OpInfo
import Veir.Data.Casting

/-!
# Puddle Patterns Validity

This file defines the obligations for a Puddle pattern to be considered valid (`Pattern.Valid`),
both structurally and semantically, using CTree-based semantics. If `Pattern.Valid` holds, then
compiling the Puddle pattern with `Pattern.compile` should produce a rewrite pattern that satisfies
`LocalRewritePattern.Valid`.
-/

namespace Veir.Puddle.CTree

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Supported Operations

This section defines the predicate `Pattern.Supported` that specify what kind of operations are
allowed in a Puddle pattern.
-/

/-- Every non-root match is pure; the root and creation operations may have memory effects.
No operation should be a terminators. -/
@[expose]
def Pattern.Supported (rule : Pattern OpCode) : Prop :=
  (∀ decl ∈ rule.matcher.decls,
    match decl with
    | .operation opCode _ _ _ _ handle _ _ =>
      HasOpInfo.isTerminator opCode = false ∧
        (handle ≠ rule.matcher.rootHandle → ∀ property, HasOpInfo.getEffects opCode property = .none)
    | _ => True) ∧
  (∀ decl ∈ rule.creation.decls,
    match decl with
    | .operation opCode .. => HasOpInfo.isTerminator opCode = false
    | _ => True)

/-!
## Matcher Semantics

The matcher constraints are written in continuation-passing style so that each generated value
remains in scope both in the updated assignment and in the final proposition.
-/

/--
The predicate of possible outcomes of an operation matched below the root: it produced `results`
when it ran in some memory, which it may have changed. A pure operation produces the same results in
every memory, but an operation reading memory, such as a load, does not, and the pattern only reuses
the results of the run it matched. This definition only makes sense for operations that have
`PureOrErr` semantics.
-/
@[expose]
def CanInterpretTo (opCode : OpCode) (property : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (results : Interp (Array RuntimeValue)) : Prop :=
  ∃ memory memory',
    PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOp' opCode property resultTypes operands #[] memory)
      (results.map (·, memory', none))
/--
Collect the constraints of a matching declaration on the given assignment,
and call the continuation with the updated assignment.
-/
@[expose]
def MatchDecl.Models (root : Handle OpCode .op) (decl : MatchDecl OpCode)
    (assignment : SemanticAssignment)
    (k : SemanticAssignment → Prop) : Prop :=
  match decl with
  | .type matcher handle =>
    ∀ type, matcher type → k (assignment.bindType handle type)
  | .value typeHandle handle =>
    match assignment.getType typeHandle with
    | some ty => ∀ value, value.Conforms ty → k (assignment.bindValue handle value ty)
    | none => False
  | .operation opCode operandHandles resultTypeHandles propertyMatcher propertyHandle opHandle
      resultHandles _ =>
    match assignment.getValues operandHandles.toList,
      assignment.getValueTypes operandHandles.toList,
      assignment.getTypes resultTypeHandles.toList with
    | some operands, some operandTypes, some resultTypes =>
      ∀ property, propertyMatcher property = true →
        IsFromVerifiedOp opCode operandTypes.toArray resultTypes.toArray property →
        /- The root operation semantics is handled outside of the matching process, as we want to
        chose the root's outcome given the creation behavior. -/
        if opHandle = root then
          k (assignment.bindProperty propertyHandle property)
        else
          assignment.ForallValues resultHandles.toList resultTypes fun results assignment =>
            CanInterpretTo opCode property resultTypes.toArray operands.toArray (.ok results.toArray) →
            k (assignment.bindProperty propertyHandle property)
    | _, _, _ => False
  | @MatchDecl.inspectOperation _ _ _ outputBundle _ _ outputs =>
    /- Ignore contextual rejection and require validity for every derived metadata value. -/
    ∀ values, k (MetadataTuple.bindSemantic (self := outputBundle) assignment outputs values)
  | MatchDecl.applyNative (hInputs := inputBundle) inputs predicate =>
    match MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs with
    | some values => predicate values = true → k assignment
    | none => False

/-- Generates matcher semantics for the given declarations, then call the continuation. -/
@[expose]
def MatchProg.ModelsDecls (root : Handle OpCode .op) (decls : List (MatchDecl OpCode))
    (assignment : SemanticAssignment) (k : SemanticAssignment → Prop) : Prop :=
  match decls with
  | [] => k assignment
  | decl :: decls =>
      MatchDecl.Models root decl assignment fun assignment =>
        MatchProg.ModelsDecls root decls assignment k

/--
Generate matcher semantics in binding order for non-root operations, and call the continuation.
Non-root operations bind successful outcomes: if they fail or trigger UB, execution never reaches
the continuation.
-/
@[expose]
def MatchProg.Models (prog : MatchProg OpCode α)
    (k : SemanticAssignment → Prop) : Prop :=
  MatchProg.ModelsDecls prog.rootHandle prog.bindingDecls SemanticAssignment.empty k

/--
Get the CTree semantics of the root operation, given an assignment and a memory state.
Returns `none` if the assignment does not contain the required values, or if the root is
not the first operation in the matcher.
-/
@[expose]
def MatchProg.rootSemantics (prog : MatchProg OpCode α) (matched : SemanticAssignment)
    (memory : MemoryState) :
    Option (Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) := do
  let .operation opCode operandHandles resultTypeHandles _ propertyHandle opHandle _ _ :: _ :=
    prog.decls | none
  if opHandle ≠ prog.rootHandle then none else do
    let operands ← matched.getValues operandHandles.toList
    let resultTypes ← matched.getTypes resultTypeHandles.toList
    let property ← matched.getProperty propertyHandle
    return Veir.CTree.interpretOp' opCode property resultTypes.toArray operands.toArray #[] memory

/-!
## Creation Semantics

This section defines `CreateProg.semantics`, which represents the semantics of a Puddle creation
program as a CTree. Like `MatchProg.Models`, it takes a `SemanticAssignment` and a continuation as
input, and call the continuation with an updated assignment.
-/

/-- Get the semantics of a creation declaration as a CTree, with a bind to the given continuation
called with an updated semantics assignment. -/
@[expose]
def CreateDecl.semantics (decl : CreateDecl OpCode) (assignment : SemanticAssignment)
    (memory : MemoryState) (next : SemanticAssignment → MemoryState → Tree α) : Tree α :=
  match decl with
  | .type value result => next (assignment.bindType result value) memory
  | .property _ value result => next (assignment.bindProperty result value) memory
  | .operation opCode operandHandles resultTypeHandles propertyHandle _ resultHandles =>
    match assignment.getValues operandHandles.toList,
      assignment.getTypes resultTypeHandles.toList, assignment.getProperty propertyHandle with
    | some operands, some resultTypes, some actualProperty => do
      let (values, memory, _) ←
        Veir.CTree.interpretOp' opCode actualProperty resultTypes.toArray operands.toArray #[] memory
      let some assignment :=
        SemanticAssignment.bindValues values assignment resultHandles.toList resultTypes | fail
      next assignment memory
    | _, _, _ => fail
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs =>
    match MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs >>= rewrite with
    | none => fail
    | some values =>
      next (MetadataTuple.bindSemantic (self := outputBundle) assignment outputs values) memory

/-- Create a CTree from a list of creation declarations. -/
@[expose]
def CreateProg.semanticsDecls (decls : List (CreateDecl OpCode))
    (assignment : SemanticAssignment) (memory : MemoryState)
    (next : SemanticAssignment → MemoryState → Tree α) : Tree α :=
  match decls with
  | [] => next assignment memory
  | decl :: decls =>
    CreateDecl.semantics decl assignment memory fun assignment memory =>
      CreateProg.semanticsDecls decls assignment memory next

/-- Resolve replacements inside the continuation, so no assignment escapes into
an intermediate return type or an opaque CTree bind. -/
@[expose]
def CreateProg.semantics (prog : CreateProg OpCode α) (replacement : Replacement OpCode)
    (assignment : SemanticAssignment) (memory : MemoryState) :
    Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  CreateProg.semanticsDecls prog.decls assignment memory fun final memory =>
    match final.getValues replacement.values.toList with
    | some values => pure (values.toArray, memory, none)
    | none => fail

/-!
## Pattern Soundness

This section defines `Pattern.PreservesSemantics`, the proposition that a Puddle pattern preserves
semantics when executed.
-/

/-- The operations created by the pattern simulate the matched root operation. -/
@[expose]
def Pattern.PreservesSemantics (rule : Pattern OpCode) : Prop :=
  MatchProg.Models rule.matcher fun matched => ∀ memory,
    match MatchProg.rootSemantics rule.matcher matched memory with
    | some source => CTree.Sim (fun target source => OperationResult.isRefinedBy source target)
        (CreateProg.semantics rule.creation rule.replacement matched memory) source
    | none => False

/-!
## Pattern Validity

`Pattern.Valid` is the predicate that a Puddle pattern is both sound structurally and
semantically. If `Pattern.Valid` holds, then compiling the Puddle pattern with `Pattern.compile`
produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

/-- The static validity conditions required by a Puddle pattern. -/
structure Pattern.Valid (rule : Pattern OpCode) : Prop where
  /-- Every operation declaration in the pattern uses a supported opcode. -/
  Supported : Pattern.Supported rule
  /-- The first executed declaration constrains the match program's root handle. -/
  ConstrainsRoot : rule.matcher.ConstrainsRoot
  /-- Structural validity of the pattern. -/
  structurallyWellFormed : rule.StructurallyWellFormed
  /-- Semantic validity of the pattern. -/
  refines : Pattern.PreservesSemantics rule
end

end Veir.Puddle.CTree
