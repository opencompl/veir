module

public import Veir.PatternRewriter.Puddle.Builders
public import Veir.Interpreter.Refinement.Lemmas
public import Veir.PatternRewriter.Puddle.Validity
public import Veir.Interpreter.CTreeRefinement
public import Veir.Dialects.LLVM.Interpreter
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
## Semantic validity

This section defines the semantic obligation `Pattern.PreservesSemantics` for Puddle patterns.

We assign runtime values to SSA value handles and concrete metadata to type and property handles.
Operation handles remain structural: their results are represented by the individual SSA value
handles. For every assignment satisfying the non-root matcher, every behavior of the creation
program must refine some behavior of the matched root. The root's metadata is fixed by the matcher,
but its runtime outcome is chosen only after the creation behavior is known.

Only non-root matched operations must be pure. The root and created operations may have memory
effects; their executions are compared at each initial memory, including the final memory.
-/

/-!
### Matcher semantics

This section defines the semantics of a matching program. The semantics are defined in terms of
propositions over `SemanticAssignment`. The semantics are written in continuation-passing style
so that each generated value remains in scope both in the updated assignment and in the final
proposition.
-/

/-- The CTree-based semantics of a single operation. -/
def interpretOpCTree (opCode : OpCode) (property : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    CTree.CTree (ErrorE ⊕ₑ UBE) FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opCode with
  | .llvm opCode => Llvm.interpretOpCTree opCode property resultTypes operands blockOperands memory
  | .builtin .unrealized_conversion_cast => do
    let some resType := resultTypes[0]? | fail
    match resType.val, operands.toList with
    | .registerType _, [.int _ (.val value)] =>
      return (#[.reg ⟨value.zeroExtend 64⟩], memory, none)
    | .registerType _, [.int _ .poison] =>
      -- Registers cannot carry poison, so any register value is possible.
      let bits : FreezeC (.mk 64) ← CTree.CTree.choose (FreezeCIn.mk 64)
      return (#[.reg ⟨bits⟩], memory, none)
    | .registerType _, [.byte width value] =>
      if value.poison = 0 then
        return (#[.reg (LLVM.Byte.toReg value)], memory, none)
      else
        -- Resolve only poisoned bits before resizing to the register width.
        let bits : FreezeC (.mk width) ← CTree.CTree.choose (FreezeCIn.mk width)
        return (#[.reg ⟨(value.val ||| (value.poison &&& bits)).zeroExtend 64⟩], memory, none)
    | .registerType _, [.addr value] =>
      match value.toInt with
      | .val bits => return (#[.reg ⟨bits⟩], memory, none)
      | .poison =>
        let bits : FreezeC (.mk 64) ← CTree.CTree.choose (FreezeCIn.mk 64)
        return (#[.reg ⟨bits⟩], memory, none)
    | .integerType width, [.reg value] =>
      return (#[.int width.bitwidth (RISCV.Reg.toInt value width.bitwidth)], memory, none)
    | .byteType width, [.reg value] =>
      return (#[.byte width.bitwidth (RISCV.Reg.toByte value width.bitwidth)], memory, none)
    | .llvmPointerType _, [.reg value] =>
      return (#[.addr (memory.ptrFromInt (.val value.val))], memory, none)
    | _, _ => fail
  | other => do
    let (values, mem, action) ←
      monadLift (Veir.interpretOp' other property resultTypes operands blockOperands memory)
    return (values, mem, action)


/-- A possible outcome of a pure operation. -/
@[expose]
def CanInterpretTo (opCode : OpCode) (property : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (results : Interp (Array RuntimeValue)) : Prop :=
  ∀ memory,
    PureOrErr.CanInterpretTo
      (interpretOpCTree opCode property resultTypes operands #[] memory)
      (results.map (·, memory, none))

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
    | some ty => ∀ value, value.Conforms ty → k (assignment.bindValue handle value)
    | none => False
  | .operation opCode operandHandles resultTypeHandles propertyMatcher propertyHandle opHandle
      resultHandles _ =>
    match assignment.getValues operandHandles.toList,
      assignment.getTypes resultTypeHandles.toList with
    | some operands, some resultTypes =>
      ∀ property, propertyMatcher property = true →
        /- The root operation semantics is handled outside of the matching process, as we want to
        chose the root's outcome given the creation behavior. -/
        if opHandle = root then
          k (assignment.bindProperty propertyHandle property)
        else
          assignment.ForallValues resultHandles.toList fun results assignment =>
            CanInterpretTo opCode property resultTypes.toArray operands.toArray (.ok results.toArray) →
            k (assignment.bindProperty propertyHandle property)
    | _, _ => False
  | @MatchDecl.inspectOperation _ _ _ outputBundle _ _ outputs =>
    /- Ignore contextual rejection and require validity for every derived metadata value. -/
    ∀ values, k (MetadataTuple.bindSemantic (self := outputBundle) assignment outputs values)
  | MatchDecl.applyNative (hInputs := inputBundle) inputs predicate =>
    match MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs with
    | some values => predicate values = true → k assignment
    | none => False

/-- Generates matcher semantics for the given declarations, then call the continuation. -/
@[expose]
def MatchProg.modelsDecls (root : Handle OpCode .op) (decls : List (MatchDecl OpCode))
    (assignment : SemanticAssignment) (k : SemanticAssignment → Prop) : Prop :=
  match decls with
  | [] => k assignment
  | decl :: decls =>
      MatchDecl.Models root decl assignment fun assignment =>
        MatchProg.modelsDecls root decls assignment k

/--
Generate matcher semantics in binding order, deferring the root's runtime outcome.
Non-root operations bind successful outcomes: if they fail or trigger UB, execution never reaches
this rewrite site. The root still binds its properties, so native metadata guards apply as usual.
-/
@[expose]
def MatchProg.Models (prog : MatchProg OpCode α)
    (k : SemanticAssignment → Prop) : Prop :=
  MatchProg.modelsDecls prog.rootHandle prog.bindingDecls SemanticAssignment.empty k

/-!
### Creation semantics

Creation programs compose operation CTrees with bind, threading assignments and memory.
Handle resolution and native construction success are checked separately, so these
construction errors cannot be hidden by interpreter failure or source undefined behavior.
Created operations are expected to verify; their runtime result arity is not checked here.
-/

/-- Bind operation results in handle order, even when the result array is symbolic.
The result count is expected to follow from verification of the created operation
and interpreter correctness, rather than a per-pattern runtime obligation. -/
@[expose]
def SemanticAssignment.bindValues (values : Array RuntimeValue)
    (assignment : SemanticAssignment) (handles : List (Handle OpCode .value))
    (index : Nat := 0) : SemanticAssignment :=
  match handles with
  | [] => assignment
  | handle :: handles =>
      bindValues values (assignment.bindValue handle values[index]!) handles (index + 1)

/-- Execute a declaration with its continuation. Assignments are substituted into
`next`, never returned through an intermediate CTree bind. Unfolding a concrete
program therefore erases handle bookkeeping without unfolding operation semantics. -/
@[expose]
def CreateDecl.interpretWith (decl : CreateDecl OpCode) (assignment : SemanticAssignment)
    (memory : MemoryState) (next : SemanticAssignment → MemoryState → Tree α) : Tree α :=
  match decl with
  | .type value result => next (assignment.bindType result value) memory
  | .property _ value result => next (assignment.bindProperty result value) memory
  | .operation opCode operandHandles resultTypeHandles propertyHandle _ resultHandles =>
    match assignment.getValues operandHandles.toList,
      assignment.getTypes resultTypeHandles.toList, assignment.getProperty propertyHandle with
    | some operands, some resultTypes, some actualProperty => do
      let (values, memory, _) ←
        interpretOpCTree opCode actualProperty resultTypes.toArray operands.toArray #[] memory
      next (SemanticAssignment.bindValues values assignment resultHandles.toList) memory
    | _, _, _ => fail
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs =>
    match MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs >>= rewrite with
    | none => fail
    | some values =>
      next (MetadataTuple.bindSemantic (self := outputBundle) assignment outputs values) memory

/-- Safety in continuation-passing form. Quantify only over operation results and
memory, and substitute the resulting assignment into the remaining obligations.
This keeps assignments out of proof goals even when operation semantics are opaque.
Control flow is restricted statically by `Pattern.Supported`, which rejects created
terminators. Connecting that restriction to the interpreter's returned action is an
interpreter correctness lemma, not a per-pattern obligation. -/
@[expose]
def CreateDecl.SafeWith (decl : CreateDecl OpCode) (assignment : SemanticAssignment)
    (memory : MemoryState) (next : SemanticAssignment → MemoryState → Prop) : Prop :=
  match decl with
  | .type value result => next (assignment.bindType result value) memory
  | .property _ value result => next (assignment.bindProperty result value) memory
  | .operation opCode operandHandles resultTypeHandles propertyHandle _ resultHandles =>
    match assignment.getValues operandHandles.toList,
      assignment.getTypes resultTypeHandles.toList, assignment.getProperty propertyHandle with
    | some operands, some resultTypes, some actualProperty =>
      ∀ values finalMemory action,
        PureOrErr.CanInterpretTo
          (interpretOpCTree opCode actualProperty resultTypes.toArray operands.toArray #[] memory)
          (.ok (values, finalMemory, action)) →
        next (SemanticAssignment.bindValues values assignment resultHandles.toList) finalMemory
    | _, _, _ => False
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs =>
    match MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs >>= rewrite with
    | none => False
    | some values =>
      next (MetadataTuple.bindSemantic (self := outputBundle) assignment outputs values) memory

/-- Execute a single declaration, retaining its final assignment for internal clients. -/
@[expose]
def CreateDecl.interpret (decl : CreateDecl OpCode) (assignment : SemanticAssignment)
    (memory : MemoryState) : Tree (SemanticAssignment × MemoryState) :=
  CreateDecl.interpretWith decl assignment memory (fun assignment memory => pure (assignment, memory))

/-- Construction obligations for a single declaration. -/
@[expose]
def CreateDecl.Safe (decl : CreateDecl OpCode) (assignment : SemanticAssignment)
    (memory : MemoryState) : Prop :=
  CreateDecl.SafeWith decl assignment memory (fun _ _ => True)

/-- Compose operation trees with bind, substituting all deterministic assignment updates. -/
@[expose]
def CreateProg.interpretDeclsWith (decls : List (CreateDecl OpCode))
    (assignment : SemanticAssignment) (memory : MemoryState)
    (next : SemanticAssignment → MemoryState → Tree α) : Tree α :=
  match decls with
  | [] => next assignment memory
  | decl :: decls =>
    CreateDecl.interpretWith decl assignment memory fun assignment memory =>
      CreateProg.interpretDeclsWith decls assignment memory next

/-- Check the remaining program at every successful operation outcome. -/
@[expose]
def CreateProg.SafeDeclsWith (decls : List (CreateDecl OpCode))
    (assignment : SemanticAssignment) (memory : MemoryState)
    (next : SemanticAssignment → MemoryState → Prop) : Prop :=
  match decls with
  | [] => next assignment memory
  | decl :: decls =>
    CreateDecl.SafeWith decl assignment memory fun assignment memory =>
      CreateProg.SafeDeclsWith decls assignment memory next

@[expose]
def CreateProg.interpretDecls (decls : List (CreateDecl OpCode))
    (assignment : SemanticAssignment) (memory : MemoryState) :
    Tree (SemanticAssignment × MemoryState) :=
  CreateProg.interpretDeclsWith decls assignment memory (fun assignment memory => pure (assignment, memory))

@[expose]
def CreateProg.SafeDecls (decls : List (CreateDecl OpCode))
    (assignment : SemanticAssignment) (memory : MemoryState) : Prop :=
  CreateProg.SafeDeclsWith decls assignment memory (fun _ _ => True)

@[expose]
def CreateProg.interpret (prog : CreateProg OpCode α) (assignment : SemanticAssignment)
    (memory : MemoryState) : Tree (SemanticAssignment × MemoryState) :=
  CreateProg.interpretDecls prog.decls assignment memory

/-- Resolve replacements inside the continuation, so no assignment escapes into
an intermediate return type or an opaque CTree bind. -/
@[expose]
def CreateProg.interpretReplacement (prog : CreateProg OpCode α) (replacement : Replacement OpCode)
    (assignment : SemanticAssignment) (memory : MemoryState) :
    Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  CreateProg.interpretDeclsWith prog.decls assignment memory fun final memory =>
    match final.getValues replacement.values.toList with
    | some values => pure (values.toArray, memory, none)
    | none => fail

/-- Check replacement resolution in the same traversal as construction safety;
never quantify over a final semantic assignment. -/
@[expose]
def CreateProg.SafeReplacement (prog : CreateProg OpCode α) (replacement : Replacement OpCode)
    (assignment : SemanticAssignment) (memory : MemoryState) : Prop :=
  CreateProg.SafeDeclsWith prog.decls assignment memory fun final _ =>
    (final.getValues replacement.values.toList).isSome

/-- Resolve the root before executing it at the same initial memory as creation.
Malformed root metadata is rejected separately from interpreter failure. -/
@[expose]
def MatchProg.interpretRoot (prog : MatchProg OpCode α) (matched : SemanticAssignment)
    (memory : MemoryState) :
    Option (Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) := do
  let .operation opCode operandHandles resultTypeHandles _ propertyHandle opHandle _ _ :: _ :=
    prog.decls | none
  if opHandle ≠ prog.rootHandle then none else do
    let operands ← matched.getValues operandHandles.toList
    let resultTypes ← matched.getTypes resultTypeHandles.toList
    let property ← matched.getProperty propertyHandle
    return interpretOpCTree opCode property resultTypes.toArray operands.toArray #[] memory

/-- Legacy memory-independent root outcome relation, retained for downstream proof helpers.
Stateful validity uses `MatchProg.interpretRoot` instead. -/
@[expose]
def MatchProg.RootCanInterpretTo (prog : MatchProg OpCode α) (matched : SemanticAssignment)
    (results : Interp (Array RuntimeValue)) : Prop :=
  match prog.decls with
  | .operation opCode operandHandles resultTypeHandles _ propertyHandle opHandle _ _ :: _ =>
    opHandle = prog.rootHandle ∧
    match matched.getValues operandHandles.toList, matched.getTypes resultTypeHandles.toList,
      matched.getProperty propertyHandle with
    | some operands, some resultTypes, some property =>
      CanInterpretTo opCode property resultTypes.toArray operands.toArray results
    | _, _, _ => False
  | _ => False

/-- Every non-root match is pure; the root and creation may have memory effects.
All operations remain non-terminators because Puddle replaces straight-line sequences. -/
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

/-- Handle resolution and native construction must succeed independently of refinement,
including when the root has UB or interpreter failure. For ordinary builders this
obligation is discharged by `provePuddleValid` without unfolding operation semantics. -/
@[expose]
def Pattern.ConstructionSafe (rule : Pattern OpCode) : Prop :=
  MatchProg.Models rule.matcher fun matched => ∀ memory,
    CreateProg.SafeReplacement rule.creation rule.replacement matched memory

/-- At each initial memory, the entire created sequence refines the root. -/
@[expose]
def Pattern.PreservesSemantics (rule : Pattern OpCode) : Prop :=
  MatchProg.Models rule.matcher fun matched => ∀ memory,
    match MatchProg.interpretRoot rule.matcher matched memory with
    | some source => Tree.Refines OperationResult.isRefinedBy source
        (CreateProg.interpretReplacement rule.creation rule.replacement matched memory)
    | none => False

/-!
## Pattern Validity

`Pattern.Valid` is the predicate that a Puddle pattern is both sound structurally and
semantically.  If `Pattern.Valid` holds, then compiling the Puddle pattern
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

/-- The static validity conditions required by a Puddle pattern. -/
structure Pattern.Valid (rule : Pattern OpCode) : Prop where
  /-- Every operation declaration in the pattern uses a supported opcode. -/
  Supported : Pattern.Supported rule
  /-- The first executed declaration constrains the match program's root handle. -/
  ConstrainsRoot : rule.matcher.ConstrainsRoot
  /-- Structural validity of the pattern. -/
  structurallyWellFormed : rule.StructurallyWellFormed
  /-- Construction bookkeeping, normally discharged automatically. Native callbacks
  may require a separate proof that they succeed. -/
  constructionSafe : Pattern.ConstructionSafe rule
  /-- Semantic validity of the pattern. -/
  refines : Pattern.PreservesSemantics rule
end

/-!
## Validity Tactics

This section defines tactics for proving the different obligations of `Pattern.Valid`. These tactics
are intended to be used in the proof of `Pattern.Valid` for a specific Puddle pattern.
-/

/-- Shared rules for assignment and monadic normalization. -/
macro "simpPuddleCore" "[" extra:Lean.Parser.Tactic.simpArg,* "]" : tactic => do
  let extra : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar,
      `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," := ⟨extra.elemsAndSeps⟩
  `(tactic| simp (config := { maxSteps := 1000000 }) only [Pattern.PreservesSemantics,
    Pattern.ConstructionSafe, MatchProg.Models,
    MatchProg.bindingDecls, List.partition_eq_filter_filter, List.range_succ, List.reverse_cons,
    MatchProg.modelsDecls, MatchDecl.Models,
    CreateProg.interpretReplacement, CreateProg.interpret, CreateProg.interpretDecls,
    CreateProg.interpretDeclsWith, CreateDecl.interpretWith,
    ↓_root_.CTree.bind_assoc, pure_bind, bind_pure,
    CreateProg.SafeReplacement, CreateProg.SafeDecls, CreateDecl.Safe,
    CreateProg.SafeDeclsWith, CreateDecl.SafeWith,
    MatchProg.interpretRoot,
    CreateDecl.interpret, bind, pure,
    Interp.ok.injEq, Interp.ub.injEq, Interp.fail.injEq,
    SemanticAssignment.getValues, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getType,
    SemanticAssignment.getProperty,
    SemanticAssignment.bindProperty, SemanticAssignment.bindType,
    SemanticAssignment.bindValue, SemanticAssignment.bind,
    SemanticAssignment.ForallValues, SemanticAssignment.bindValues,
    MetadataTuple.resolveSemantic, MetadataTuple.Shape.resolveSemantic,
    MetadataTuple.Atom.resolveSemantic, MetadataTuple.bindSemantic,
    MetadataTuple.Shape.bindSemantic, MetadataTuple.Atom.bindSemantic,
    MatchProg.RootCanInterpretTo,
    SemanticAssignment.bind_of_ne_eq,
    /- TypeAttr cast normalization -/
    IsTypeAttr.cast?_eq_some_iff,
    /- Native metadata tuples -/
    IsMetadataTuple.shape_unit, IsMetadataTuple.shape_type, IsMetadataTuple.shape_property,
    IsMetadataTuple.shape_type_cons, IsMetadataTuple.shape_property_cons,
    /- Concrete lists, arrays, options -/
    List.filter_cons_of_pos, List.filter_cons_of_neg, List.filter_nil, Function.comp_apply,
    List.reverse_nil, List.nil_append, List.cons_append, List.append_nil,
    Array.toList_map, Array.toList_range, List.range_zero, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil,
    Array.size_map, Array.size_range,
    List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Option.bind_fun_some, Nat.add_zero, Nat.reduceAdd, Nat.zero_ne_one, Nat.reduceEqDiff,
    Option.map_some, Option.map_eq_some_iff, Option.getD_eq_iff,
    /- Propositional normalization -/
    Bool.not_true, Bool.not_false, Bool.not_eq_true, Bool.not_eq_true', Bool.false_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_false, or_false,
    not_false_eq_true, not_true_eq_false, ne_eq, reduceCtorEq, ↓reduceIte, ↓reduceDIte, forall_const,
    and_true, and_imp, not_imp, Classical.not_forall, not_exists, not_and, exists_and_left,
    exists_false, false_or, exists_eq_left, exists_eq_right,
    forall_exists_index, forall_apply_eq_imp_iff, forall_eq_apply_imp_iff, true_and,
    /- Elementwise array refinement -/
    RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.arrayIsRefinedBy_refl,
    /- Handle equality injectivity -/
    Handle.mk.injEq, $extra,*])

end Veir.Puddle.CTree
