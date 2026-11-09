module

public import Veir.PatternRewriter.Puddle.HandleContextLemmas
public import Veir.PatternRewriter.Puddle.CreationSemanticsCongr
public import Veir.PatternRewriter.Puddle.CreationOperationSemantics
public import Veir.PatternRewriter.Puddle.ExecutionBounds
public import Veir.Interpreter.CTreeFunctionRefinement
public import Veir.Interpreter.Refinement.CTree
public import Veir.Interpreter.CTreeMemoryPreservation
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.CTreeInterpreter
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.MatcherSemantics

namespace Veir.Puddle

public section

theorem HandleContext.require_of_forbid {defined : HandleContext}
    {kind queriedKind : HandleType OpCode} {handle : Handle OpCode kind}
    {queried : Handle OpCode queriedKind}
    (required : (defined.forbid handle).require queried = true) :
    defined.require queried = true ∧ queried.id ≠ handle.id := by
  simp only [HandleContext.require, HandleContext.forbid, decide_eq_true_eq,
    List.mem_cons, not_or] at required
  refine ⟨?_, required.2.1⟩
  simp only [HandleContext.require, decide_eq_true_eq]
  exact ⟨by simpa [HandleContext.lookup] using required.1, required.2.2⟩

theorem HandleContext.require_of_forbidMany {defined : HandleContext}
    {kind queriedKind : HandleType OpCode} (handles : List (Handle OpCode kind))
    {queried : Handle OpCode queriedKind}
    (required : (defined.forbidMany handles).require queried = true) :
    defined.require queried = true ∧ queried.id ∉ handles.map Handle.id := by
  induction handles generalizing defined with
  | nil => exact ⟨required, by simp⟩
  | cons first rest ih =>
    have ht := ih (defined := defined.forbid first) required
    have hf := HandleContext.require_of_forbid ht.1
    exact ⟨hf.1, by simp [hf.2, ht.2]⟩

/-- Root results unavailable to creation need no semantic binding in the replayed matcher. -/
theorem HandleContext.AgreesOn.for_creation {defined : HandleContext}
    {root : Handle OpCode .op} {results : Array (Handle OpCode .value)}
    {a b : SemanticAssignment} (agree : defined.AgreesOn (results.toList.map Handle.id) a b) :
    ((defined.forbid root).forbidMany results.toList).AgreesOn [] a b := by
  intro kind queried notOp required _
  obtain ⟨hforbiddenRoot, hnotResults⟩ := HandleContext.require_of_forbidMany results.toList required
  have havailable := (HandleContext.require_of_forbid hforbiddenRoot).1
  exact agree kind queried notOp havailable hnotResults

/-- Structural validity supplies the concrete creation-input context and checked replacement. -/
theorem Pattern.creation_check_of_structurallyWellFormed {rule : Pattern OpCode}
    (wellFormed : rule.StructurallyWellFormed) :
    ∃ before after, rule.matcher.collectBindings = some before ∧
      rule.creation.checkBindings before = some after ∧ rule.replacement.checkBindings after = true := by
  have hex : ∃ final, rule.checkStructure = some final := by
    cases h : rule.checkStructure with
    | none => simp [Pattern.StructurallyWellFormed, h] at wellFormed
    | some final => exact ⟨final, rfl⟩
  obtain ⟨final, hfinal⟩ := hex
  simp only [Pattern.checkStructure, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hfinal
  obtain ⟨before, hb, after, ha, u, hguard, _⟩ := hfinal
  refine ⟨before, after, hb, ha, ?_⟩
  simpa [guard] using hguard

namespace CTree

/-- A successfully matched valid pattern constrains a nonterminating root opcode. -/
theorem Pattern.Valid.root_nonterminator_of_interpret {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule) {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacementPointers : Array ValuePtr}
    (run : rule.interpret ctx root = some (newCtx, some (newOps, replacementPointers))) :
    (root.getOpType! ctx.raw).isTerminator = false := by
  have constrains := valid.ConstrainsRoot
  cases decls : rule.matcher.decls with
  | nil => simp [Veir.Puddle.MatchProg.ConstrainsRoot, decls] at constrains
  | cons decl rest =>
    cases decl with
    | operation code operands types matcher property handle results count =>
      have sameCode : root.getOpType! ctx.raw = code := by
        by_cases same : root.getOpType! ctx.raw = code
        · exact same
        · simp [Veir.Puddle.Pattern.interpret, Veir.Puddle.MatchProg.run, decls, guard,
            same, failure, Option.bind] at run
      rw [sameCode]
      exact (valid.Supported.1
        (.operation code operands types matcher property handle results count)
        (by simp [decls])).1
    | type matcher handle => simp [Veir.Puddle.MatchProg.ConstrainsRoot, decls] at constrains
    | value ty handle => simp [Veir.Puddle.MatchProg.ConstrainsRoot, decls] at constrains
    | inspectOperation op inspect outputs => simp [Veir.Puddle.MatchProg.ConstrainsRoot, decls] at constrains
    | applyNative inputs predicate => simp [Veir.Puddle.MatchProg.ConstrainsRoot, decls] at constrains

/-- Successful concrete matching identifies the symbolic root tree with the original raw opcode. -/
theorem MatchProg.rootSemantics_of_run {prog : Veir.Puddle.MatchProg OpCode α}
    (constrains : prog.ConstrainsRoot) {ctx : IRContext OpCode} {root : OperationPtr}
    {matched : Assignment OpCode} (resolve : ValueResolver)
    (run : prog.run ctx root = some matched) {operandValues : List RuntimeValue}
    (resolved : (root.getOperands! ctx).toList.mapM resolve = some operandValues)
    (memory : MemoryState) :
    MatchProg.rootSemantics prog (matched.denote resolve (fun p => some (p.getType! ctx))) memory =
      some (Veir.CTree.interpretOp' (root.getOpType! ctx)
        (root.getProperties! ctx (root.getOpType! ctx)) (root.getResultTypes! ctx)
        operandValues.toArray #[] memory) := by
  have originalRun := run
  cases hdecls : prog.decls with
  | nil => simp [Veir.Puddle.MatchProg.ConstrainsRoot, hdecls] at constrains
  | cons decl rest =>
    cases decl with
    | operation code operands types matcher property op results count =>
      have hroot : op = prog.rootHandle := by
        simpa [Veir.Puddle.MatchProg.ConstrainsRoot, hdecls] using constrains
      subst op
      simp only [Veir.Puddle.MatchProg.run, hdecls, Veir.Puddle.MatchProg.runDecls,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at run
      obtain ⟨u, _, initial, _, middle, hfirst, htail⟩ := run
      obtain ⟨actual, hop, hcode, _, hoperands, htypes, hproperty, _⟩ :=
        Veir.Puddle.MatchDecl.operation_fields_of_run hfirst
      have preserved := Assignment.Extends.of_runDecls htail
      have hopFinal := preserved.getOp hop
      have hrootFinal := Veir.Puddle.MatchProg.getOp_root_of_run prog originalRun
      have heq : actual = root := Option.some.inj (hopFinal.symm.trans hrootFinal)
      subst actual
      have hv : (matched.denote resolve (fun p => some (p.getType! ctx))).getValues operands.toList = some operandValues := by
        rw [Assignment.denote_getValues (typeOf := fun p => some (p.getType! ctx)), preserved.getValues hoperands]
        exact resolved
      have ht : (matched.denote resolve (fun p => some (p.getType! ctx))).getTypes types.toList = some (root.getResultTypes! ctx).toList := by
        rw [Assignment.denote_getTypes (typeOf := fun p => some (p.getType! ctx)), preserved.getTypes htypes]; rfl
      have hp := (Assignment.denote_getProperty matched resolve property (fun p => some (p.getType! ctx))).trans (preserved.getProperty hproperty)
      subst code
      simp [MatchProg.rootSemantics, hdecls, hv, ht, hp]
    | value ty handle => simp [Veir.Puddle.MatchProg.ConstrainsRoot, hdecls] at constrains
    | type matcher handle => simp [Veir.Puddle.MatchProg.ConstrainsRoot, hdecls] at constrains
    | inspectOperation op inspect outputs => simp [Veir.Puddle.MatchProg.ConstrainsRoot, hdecls] at constrains
    | applyNative inputs predicate => simp [Veir.Puddle.MatchProg.ConstrainsRoot, hdecls] at constrains

/-- Local soundness for the actual operations returned by successful matcher and creation runs.
The source root tree is extracted from the same concrete matcher assignment. -/
theorem Pattern.Valid.createdOps_sim_rootSemantics {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule) {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    {matched final : Assignment OpCode} {newOps : Array OperationPtr}
    (resolve : ValueResolver) (memory : MemoryState)
    (matchRun : rule.matcher.run ctx.raw root = some matched)
    (createRun : rule.creation.run matched ctx = some (newCtx, newOps, final))
    (inBounds : matched.ValuesInBounds ctx.raw)
    (equations : ∀ decl ∈ rule.matcher.decls,
      MatchDecl.RuntimeEquations ctx.raw rule.matcher.rootHandle resolve matched decl)
    {source : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)}
    (rootTree : MatchProg.rootSemantics rule.matcher
      (matched.denote resolve (fun p => some (p.getType! ctx.raw))) memory = some source) :
    _root_.CTree.Sim (fun target source => OperationResult.isRefinedBy source target)
      (interpretCreatedOps newCtx.raw newOps.toList resolve memory (fun r m =>
        match final.getValues rule.replacement.values >>= fun pointers => pointers.toList.mapM r with
        | some values => pure (values.toArray, m, none)
        | none => fail)) source := by
  obtain ⟨results, defined, semantic, hresults, hdefined, hrealizes, hagree, _, hrootEq⟩ :=
    Pattern.Valid.realizes_of_run_with_rootSemantics valid resolve matchRun equations
  have hsource : MatchProg.rootSemantics rule.matcher semantic memory = some source :=
    (hrootEq memory).trans rootTree
  have hsim := Pattern.Valid.refines_of_realizes valid hrealizes memory hsource
  obtain ⟨before, after, hbefore, hchecked, hreplacement⟩ :=
    Veir.Puddle.Pattern.creation_check_of_structurallyWellFormed valid.structurallyWellFormed
  have hbeforeEq : before = (defined.forbid rule.matcher.rootHandle).forbidMany results.toList := by
    simp only [Veir.Puddle.MatchProg.collectBindings, hresults, hdefined, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at hbefore
    exact hbefore.symm
  subst before
  have hcreation := CreateProg.semantics_congr rule.creation rule.replacement hchecked hreplacement
    hagree.for_creation memory
  rw [hcreation, CreateProg.semantics_eq_returnedOps rule.creation rule.replacement resolve memory
    inBounds createRun] at hsim
  exact hsim

/-- Successful concrete creation refines the original matched root's raw opcode semantics. -/
theorem Pattern.Valid.createdOps_sim_originalRoot {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule) {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    {matched final : Assignment OpCode} {newOps : Array OperationPtr}
    (resolve : ValueResolver) (memory : MemoryState)
    (matchRun : rule.matcher.run ctx.raw root = some matched)
    (createRun : rule.creation.run matched ctx = some (newCtx, newOps, final))
    (inBounds : matched.ValuesInBounds ctx.raw)
    (equations : ∀ decl ∈ rule.matcher.decls,
      MatchDecl.RuntimeEquations ctx.raw rule.matcher.rootHandle resolve matched decl)
    {operandValues : List RuntimeValue}
    (resolved : (root.getOperands! ctx.raw).toList.mapM resolve = some operandValues) :
    _root_.CTree.Sim (fun target source => OperationResult.isRefinedBy source target)
      (interpretCreatedOps newCtx.raw newOps.toList resolve memory (fun r m =>
        match final.getValues rule.replacement.values >>= fun pointers => pointers.toList.mapM r with
        | some values => pure (values.toArray, m, none)
        | none => fail))
      (Veir.CTree.interpretOp' (root.getOpType! ctx.raw)
        (root.getProperties! ctx.raw (root.getOpType! ctx.raw)) (root.getResultTypes! ctx.raw)
        operandValues.toArray #[] memory) :=
  Pattern.Valid.createdOps_sim_rootSemantics valid resolve memory matchRun createRun inBounds equations
    (MatchProg.rootSemantics_of_run valid.ConstrainsRoot resolve matchRun resolved memory)

/-- A successful concrete local-pattern execution returns operations and replacement pointers
whose raw execution refines the original root operation. -/
theorem Pattern.Valid.interpret_createdOps_sim_originalRoot {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule) {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacementPointers : Array ValuePtr}
    (resolve : ValueResolver) (memory : MemoryState)
    (localRun : rule.interpret ctx root = some (newCtx, some (newOps, replacementPointers)))
    (rootInBounds : root.InBounds ctx.raw)
    (executionFacts : ∀ matched, rule.matcher.run ctx.raw root = some matched →
      ∀ decl ∈ rule.matcher.decls,
        MatchDecl.RuntimeEquations ctx.raw rule.matcher.rootHandle resolve matched decl)
    {operandValues : List RuntimeValue}
    (resolved : (root.getOperands! ctx.raw).toList.mapM resolve = some operandValues) :
    _root_.CTree.Sim (fun target source => OperationResult.isRefinedBy source target)
      (interpretCreatedOps newCtx.raw newOps.toList resolve memory (fun r m =>
        match replacementPointers.toList.mapM r with
        | some values => pure (values.toArray, m, none)
        | none => fail))
      (Veir.CTree.interpretOp' (root.getOpType! ctx.raw)
        (root.getProperties! ctx.raw (root.getOpType! ctx.raw)) (root.getResultTypes! ctx.raw)
        operandValues.toArray #[] memory) := by
  cases hmatch : rule.matcher.run ctx.raw root with
  | none => simp [Veir.Puddle.Pattern.interpret, hmatch] at localRun
  | some matched =>
    cases hcreate : rule.creation.run matched ctx with
    | none => simp [Veir.Puddle.Pattern.interpret, hmatch, hcreate] at localRun
    | some created =>
      rcases created with ⟨actualCtx, actualOps, final⟩
      cases hreplacements : final.getValues rule.replacement.values with
      | none => simp [Veir.Puddle.Pattern.interpret, hmatch, hcreate, hreplacements] at localRun
      | some pointers =>
        simp only [Veir.Puddle.Pattern.interpret, hmatch, hcreate, hreplacements,
          Option.some.injEq, Prod.mk.injEq] at localRun
        rcases localRun with ⟨rfl, rfl, rfl⟩
        have hbound := (rule.matcher.inBounds_of_run rootInBounds hmatch).values
        have hequations := executionFacts matched hmatch
        have hsim := Pattern.Valid.createdOps_sim_originalRoot valid resolve memory hmatch hcreate
          hbound hequations resolved
        simpa only [hreplacements, Option.bind_eq_bind, Option.bind_some] using hsim

/-- A rejected compiled match preserves the verified module's CTree semantics. -/
theorem Pattern.compile_noMatch_moduleRefinement (rule : Veir.Puddle.Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {op moduleOp : OperationPtr}
    (opIn : op.InBounds rewriter.ctx.raw) (verified : rewriter.ctx.Verified moduleOp)
    (noMatch : rule.matcher.run rewriter.ctx.raw op = none)
    (run : rule.compile.run rewriter op opIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx := by
  rw [Veir.Puddle.Pattern.compile_run_of_no_match rule rewriter op opIn noMatch] at run
  cases run
  exact OperationPtr.isModuleRefinedByCTree_refl verified moduleOp

/-- Local execution remains sound when its inputs and memory refine the source execution.
This composes pattern validity with primitive refinement at the original root. -/
theorem Pattern.Valid.interpret_createdOps_sim_refiningInputs
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacementPointers : Array ValuePtr}
    (resolve : ValueResolver) (sourceMemory targetMemory : MemoryState)
    (localRun : rule.interpret ctx root = some (newCtx, some (newOps, replacementPointers)))
    (rootIn : root.InBounds ctx.raw) (rootVerified : root.Verified ctx rootIn)
    (executionFacts : ∀ matched, rule.matcher.run ctx.raw root = some matched →
      ∀ decl ∈ rule.matcher.decls,
        MatchDecl.RuntimeEquations ctx.raw rule.matcher.rootHandle resolve matched decl)
    {targetValues : List RuntimeValue}
    (resolved : (root.getOperands! ctx.raw).toList.mapM resolve = some targetValues)
    (sourceValues : Array RuntimeValue)
    (conforms : RuntimeValue.ArrayConforms sourceValues (root.getOperandTypes! ctx.raw))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues.toArray)
    (memory : sourceMemory.isRefinedBy targetMemory) :
    _root_.CTree.Sim (fun target source => OperationResult.isRefinedBy source target)
      (interpretCreatedOps newCtx.raw newOps.toList resolve targetMemory (fun r m =>
        match replacementPointers.toList.mapM r with
        | some results => pure (results.toArray, m, none)
        | none => fail))
      (Veir.OperationPtr.interpretCTree root rootIn sourceValues sourceMemory) := by
  have localSimulation := valid.interpret_createdOps_sim_originalRoot resolve targetMemory
    localRun rootIn executionFacts resolved
  have primitive := Veir.OpCode.interpretCTree_monotone_assumed
    (root.getOpType ctx.raw rootIn) ctx root rootIn rfl rootVerified
    sourceValues targetValues.toArray sourceMemory targetMemory conforms values memory
  have rootTree : Veir.OperationPtr.interpretCTree root rootIn targetValues.toArray targetMemory =
      Veir.CTree.interpretOp' (root.getOpType! ctx.raw)
        (root.getProperties! ctx.raw (root.getOpType! ctx.raw)) (root.getResultTypes! ctx.raw)
        targetValues.toArray #[] targetMemory := by
    unfold Veir.OperationPtr.interpretCTree
    have codeEq := OperationPtr.getOpType!_eq_getOpType rootIn
    have propertyEq := OperationPtr.getProperties!_eq_getProperties rootIn
      (opCode := root.getOpType ctx.raw rootIn)
      (by simpa only [ofDialect_hasDialectRefl] using codeEq)
    simp only [← propertyEq, ← OperationPtr.getResultTypes!_eq_getResultTypes rootIn,
      ← OperationPtr.getSuccessors!_eq_getSuccessors rootIn]
    rw [← codeEq]
    rw [Veir.CTree.interpretOp'_successors_irrelevant _ _ _ _ _ #[] _ _
      (valid.root_nonterminator_of_interpret localRun)]
    rfl
  rw [← rootTree] at localSimulation
  exact _root_.CTree.Sim.trans localSimulation primitive (fun target intermediate source localRef primitiveRef =>
    OperationResult.isRefinedBy_trans primitiveRef.1
      localRef)


end CTree

end

end Veir.Puddle
