module

public import Veir.PatternRewriter.Puddle.Builders
public import Veir.Interpreter.Refinement.Lemmas
public import Veir.PatternRewriter.Puddle.Validity
public import Veir.PatternRewriter.Puddle.CreationM
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

Note that we assume that any `Supported` operation has at least one behavior, so we do not check
that the newly created operations have at least one behavior.
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

Creation programs execute in `CreationM`, collecting possible interpreter outcomes and construction
obligations. Assignment updates are deterministic monadic steps; the final computation resolves
replacement runtime values before checking refinement.
-/

/-- Bind operation results in handle order, even when the result array is symbolic.
The caller checks the result count separately. -/
@[expose]
def SemanticAssignment.bindValues (values : Array RuntimeValue)
    (assignment : SemanticAssignment) (handles : List (Handle OpCode .value))
    (index : Nat := 0) : SemanticAssignment :=
  match handles with
  | [] => assignment
  | handle :: handles =>
      bindValues values (assignment.bindValue handle values[index]!) handles (index + 1)

/-- Execute a creation declaration, collecting its possible outcomes and construction obligations. -/
@[expose]
def CreateDecl.interpret (decl : CreateDecl OpCode) (assignment : SemanticAssignment) :
    CreationM SemanticAssignment :=
  match decl with
  | .type value result => pure (assignment.bindType result value)
  | .property _ value result => pure (assignment.bindProperty result value)
  | .operation opCode operandHandles resultTypeHandles propertyHandle _ resultHandles =>
    match assignment.getValues operandHandles.toList,
      assignment.getTypes resultTypeHandles.toList, assignment.getProperty propertyHandle with
    | some operands, some resultTypes, some actualProperty => do
      let values ← CreationM.choose
        (CanInterpretTo opCode actualProperty resultTypes.toArray operands.toArray)
      CreationM.checked (resultHandles.size = values.size)
        (SemanticAssignment.bindValues values assignment resultHandles.toList 0)
    | _, _, _ => CreationM.invalid
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs =>
    match MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs >>= rewrite with
    | none => CreationM.invalid
    | some values => pure (MetadataTuple.bindSemantic (self := outputBundle) assignment outputs values)

/-- Execute creation declarations in order. The monad propagates errors and stops execution. -/
@[expose]
def CreateProg.interpretDecls (decls : List (CreateDecl OpCode)) (assignment : SemanticAssignment) :
    CreationM SemanticAssignment := do
  match decls with
  | [] => pure assignment
  | decl :: decls =>
    let assignment ← CreateDecl.interpret decl assignment
    CreateProg.interpretDecls decls assignment

@[expose]
def CreateProg.interpret (prog : CreateProg OpCode α) (assignment : SemanticAssignment) :
    CreationM SemanticAssignment :=
  CreateProg.interpretDecls prog.decls assignment

/-- Return replacement runtime values, so the final postcondition needs no assignment. -/
@[expose]
def CreateProg.interpretReplacement (prog : CreateProg OpCode α) (replacement : Replacement OpCode)
    (assignment : SemanticAssignment) : CreationM (Array RuntimeValue) := do
  let final ← CreateProg.interpret prog assignment
  match final.getValues replacement.values.toList with
  | some values => pure values.toArray
  | none => CreationM.invalid

/-- Interpret the root with the operands, types, and properties fixed by the matcher. -/
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

/--
For every non-root matched behavior and every creation behavior, some root behavior is refined.
-/
@[expose]
def Pattern.PreservesSemantics (rule : Pattern OpCode) : Prop :=
  MatchProg.Models rule.matcher fun matched =>
    (CreateProg.interpretReplacement rule.creation rule.replacement matched).Models
      (fun target => ∃ source, MatchProg.RootCanInterpretTo rule.matcher matched source ∧
        Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy source target)

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
  /-- The first executed declaration constrains the match program's root handle. -/
  ConstrainsRoot : rule.matcher.ConstrainsRoot
  /-- Structural validity of the pattern. -/
  structurallyWellFormed : rule.StructurallyWellFormed
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
  `(tactic| simp (config := { maxSteps := 1000000 }) only [Pattern.PreservesSemantics, MatchProg.Models,
    MatchProg.bindingDecls, List.partition_eq_filter_filter, List.range_succ, List.reverse_cons,
    MatchProg.modelsDecls, MatchDecl.Models,
    CreateProg.interpretReplacement, CreateProg.interpret, CreateProg.interpretDecls,
    ↓CreationM.bind_assoc, ↓CreationM.pure_bind, ↓CreationM.bind_pure,
    ↓CreationM.invalid_bind,
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
    not_false_eq_true, ne_eq, reduceCtorEq, ↓reduceIte, ↓reduceDIte, forall_const,
    and_true, and_imp, not_imp, Classical.not_forall, not_exists, not_and, exists_and_left,
    exists_false, false_or, exists_eq_left, exists_eq_right,
    forall_exists_index, forall_apply_eq_imp_iff, forall_eq_apply_imp_iff, true_and,
    /- Elementwise array refinement -/
    RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.arrayIsRefinedBy_refl,
    /- Handle equality injectivity -/
    Handle.mk.injEq, $extra,*])

end Veir.Puddle.CTree
