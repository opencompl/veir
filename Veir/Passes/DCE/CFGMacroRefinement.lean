module

public import Veir.Passes.DCE.CFGRefinement
public import Veir.Passes.DCE.MacroSuffix
public import Veir.Passes.DCE.Traversal

public section

namespace Veir.DCE

/-- Identify the current source operation; block-entry states carry no operation. -/
@[expose]
def cfgOperationAt {ctx : WfIRContext OpCode} :
    CTree.interpretCFG.StateLocation ctx × InterpreterState ctx → Option OperationPtr
  | (.inl _, _) => none
  | (.inr ⟨operation, _⟩, _) => some operation

/-- A grouped execution starting at a deleted operation remains sequential,
preserves all final-live values, and traverses only deleted source operations. -/
theorem MacroRun.deleted_frame
    {sourceCtx targetCtx : WfIRContext OpCode} (erases : Erasures sourceCtx targetCtx)
    (allowed : OperationPtr → Prop)
    (hallowed : ∀ operation, allowed operation → ¬ operation.InBounds targetCtx.raw)
    {initial : CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx}
    {result : (CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx) ⊕
      (InterpreterState sourceCtx × Array RuntimeValue)}
    (run : MacroRun cfgOperationAt
      (fun (location, state) => CTree.interpretCFGTreeStep location state) allowed initial result) :
    ∀ (operation : OperationPtr), cfgOperationAt initial = some operation →
      ¬ operation.InBounds targetCtx.raw → ∀ target : InterpreterState targetCtx,
      StatesRefineOn (fun value => value.InBounds targetCtx.raw) initial.2 target →
      match result with
      | .inl next => ∃ nextOperation,
        cfgOperationAt next = some nextOperation ∧
        StatesRefineOn (fun value => value.InBounds targetCtx.raw) next.2 target ∧
        Skips sourceCtx targetCtx (some operation) (some nextOperation)
      | .inr _ => False := by
  induction run with
  | @base initial result executes =>
    intro operation identifies deleted target hstate
    rcases initial with ⟨location, source⟩
    cases location with
    | inl block => cases identifies
    | inr sourceOperation =>
      rcases sourceOperation with ⟨sourceOperation, sourceIn⟩
      have : sourceOperation = operation := Option.some.inj identifies
      subst sourceOperation
      obtain ⟨next, nextIn, nextState, hnext, rfl, hstates⟩ :=
        interpretCFGTreeStep_deleted_frame erases operation source target sourceIn deleted hstate result executes
      refine ⟨next, rfl, hstates, .step operation sourceIn deleted ?_⟩
      have hnext' : operation.getNextOp! sourceCtx.raw = some next := by simpa only [eq_bang] using hnext
      rw [hnext']
      exact .refl _
  | @splice initial middle result selected first identifies admitted rest ihFirst ihRest =>
    intro operation hinitial deleted target hstate
    obtain ⟨middleOperation, hmiddle, hstates, hpath⟩ :=
      ihFirst operation hinitial deleted target hstate
    have : middleOperation = selected := by grind
    subst middleOperation
    have hrest := ihRest selected identifies (hallowed selected admitted) target hstates
    cases result with
    | inr returned => exact hrest
    | inl next =>
      obtain ⟨nextOperation, hnext, hstates, hrest⟩ := hrest
      exact ⟨nextOperation, hnext, hstates, hpath.trans hrest⟩

end Veir.DCE

namespace Veir.DCE

/-- Original next-operation chains have a unique endpoint once all deleted
operations have been skipped. `none` is a normal endpoint as well. -/
theorem Skips.finish_unique {source target : WfIRContext OpCode} {start firstFinish secondFinish}
    (first : Skips source target start firstFinish) (second : Skips source target start secondFinish)
    (hfirst : ∀ operation, firstFinish = some operation → operation.InBounds target.raw)
    (hsecond : ∀ operation, secondFinish = some operation → operation.InBounds target.raw) :
    firstFinish = secondFinish := by
  induction first generalizing secondFinish with
  | refl finish =>
    cases second with
    | refl => rfl
    | step operation original deleted rest => exact False.elim (deleted (hfirst operation rfl))
  | @step operation original deleted firstFinish rest ih =>
    cases second with
    | refl => exact False.elim (deleted (hsecond operation rfl))
    | step operation original' deleted' secondRest => exact ih secondRest hfirst hsecond

end Veir.DCE

namespace Veir.DCE

/-- A suffix either does nothing or starts a grouped execution at an admitted
operation. In particular, it cannot change a block entry or a return value. -/
theorem SuffixRun.eq_or_macroRun {operationAt : ι → Option OperationPtr}
    {body : ι → Tree (ι ⊕ α)} {allowed : OperationPtr → Prop} {initial result}
    (run : SuffixRun operationAt body allowed initial result) :
    result = initial ∨ ∃ location operation, initial = .inl location ∧
      operationAt location = some operation ∧ allowed operation ∧
      MacroRun operationAt body allowed location result := by
  induction run with
  | stop => exact .inl rfl
  | @splice middle result selected first identifies admitted rest ih =>
    cases ih with
    | inl equal =>
      subst initial
      exact .inr ⟨middle, selected, rfl, identifies, admitted, rest⟩
    | inr continued =>
      obtain ⟨location, operation, hinitial, identifiesInitial, hallowed, hfirst⟩ := continued
      exact .inr ⟨location, operation, hinitial, identifiesInitial, hallowed,
        .splice hfirst identifies admitted rest⟩

end Veir.DCE

namespace Veir.DCE

/-- A successful normalized suffix starting at an original operation reaches
the unique normal endpoint of its original next-operation chain. -/
theorem macroSuffix_operation_success
    {sourceCtx targetCtx : WfIRContext OpCode} (erases : Erasures sourceCtx targetCtx)
    (operations : List OperationPtr)
    (hdeleted : ∀ operation ∈ operations, ¬ operation.InBounds targetCtx.raw)
    (operation : OperationPtr) (sourceIn : operation.InBounds sourceCtx.raw)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (hstate : StatesRefineOn (fun value => value.InBounds targetCtx.raw) source target)
    (finish : Option OperationPtr) (hpath : Skips sourceCtx targetCtx (some operation) finish)
    (hfinish : ∀ endpoint, finish = some endpoint → endpoint.InBounds targetCtx.raw)
    (result : (CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx) ⊕
      (InterpreterState sourceCtx × Array RuntimeValue))
    (executes : PureOrErr.CanInterpretTo
      (macroSuffix cfgOperationAt (fun (location, state) => CTree.interpretCFGTreeStep location state)
        operations (.inl (.inr ⟨operation, sourceIn⟩, source))) (.ok result))
    (hnormal : ∀ next endpoint, result = .inl next → cfgOperationAt next = some endpoint →
      endpoint.InBounds targetCtx.raw) :
    ∃ (endpoint : OperationPtr) (endpointIn : endpoint.InBounds sourceCtx.raw)
      (nextState : InterpreterState sourceCtx),
      result = .inl (.inr ⟨endpoint, endpointIn⟩, nextState) ∧ some endpoint = finish ∧
      StatesRefineOn (fun value => value.InBounds targetCtx.raw) nextState target := by
  have run := macroSuffix_success_run (cfgOperationAt (ctx := sourceCtx))
    (fun (location, state) => CTree.interpretCFGTreeStep location state) operations _ _ executes
  rcases run.eq_or_macroRun with unchanged | ⟨location, removed, hinitial, identifies, admitted, continued⟩
  · subst result
    have hendpoint := hnormal (.inr ⟨operation, sourceIn⟩, source) operation rfl rfl
    have equal := Skips.finish_unique (.refl (some operation)) hpath
      (by intro op h; cases Option.some.inj h; exact hendpoint) hfinish
    exact ⟨operation, sourceIn, source, rfl, equal, hstate⟩
  · have hlocation : location = (.inr ⟨operation, sourceIn⟩, source) := Sum.inl.inj hinitial.symm
    subst location
    have hremoved : removed = operation := (Option.some.inj identifies).symm
    subst removed
    have hframed := continued.deleted_frame erases (fun op => op ∈ operations)
      hdeleted operation rfl (hdeleted operation admitted) target hstate
    cases result with
    | inr returned => cases hframed
    | inl next =>
      obtain ⟨endpoint, identifiesEndpoint, hstates, endpointPath⟩ := hframed
      rcases next with ⟨nextLocation, nextState⟩
      cases nextLocation with
      | inl block => cases identifiesEndpoint
      | inr nextOperation =>
        rcases nextOperation with ⟨nextOperation, nextIn⟩
        have : nextOperation = endpoint := Option.some.inj identifiesEndpoint
        subst endpoint
        have hendpoint := hnormal (.inr ⟨nextOperation, nextIn⟩, nextState) nextOperation rfl rfl
        have equal := Skips.finish_unique endpointPath hpath
          (by intro op h; cases Option.some.inj h; exact hendpoint) hfinish
        exact ⟨nextOperation, nextIn, nextState, rfl, equal, hstates⟩

end Veir.DCE
