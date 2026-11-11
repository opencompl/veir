module

public import Veir.Interpreter.CTreeRefinement.Lifted
public import Veir.Interpreter.CTreeRefinement.CFGSim
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Monotonicity
import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Lists of operations as closed trees

The closed CFG loop runs the operations of a block one step at a time. Grouped into one step per
block (`blockStep`), a block call runs the list of its operations, which `opListTree` runs as a
tree, as `interpretOpList` runs it in `Interp`. A transformation that changes the operations of a
block can then be shown correct on lists, as for `Interp`.

`Returns t P` says that every behavior of `t` returns a value satisfying `P`. It describes the
target side of a simulation step whose target has no counterpart in the source, such as an
operation that the transformation inserted.
-/

open CTree

namespace Veir.CTree

/-! ## Trees that return only certain values -/

/--
Every behavior of `t` returns a value that satisfies `P`: `t` has no undefined behavior, does not
fail, and returns only values that satisfy `P`.
-/
abbrev Returns (t : Tree α) (P : α → Prop) : Prop :=
  Sim (fun a (_ : Unit) => P a) t (pure () : Tree Unit)


@[simp]
theorem returns_pure {a : α} {P : α → Prop} : Returns (pure a : Tree α) P ↔ P a :=
  Sim.pure _ _ _

/-- A tree followed by a continuation that returns only values satisfying `Q` for what it may
return. -/
theorem Returns.bind {t : Tree α} {P : α → Prop} {k : α → Tree β} {Q : β → Prop}
    (h : Returns t P) (hk : ∀ a, P a → Returns (k a) Q) : Returns (t >>= k) Q := by
  have := Sim.bind (RR' := fun b (_ : Unit) => Q b) t (pure ()) k (fun _ => pure ()) h
    (fun a _ ha => hk a ha)
  rw [CTree.bind_pure] at this
  rwa [tree_bind_eq]

theorem Returns.mono {t : Tree α} {P Q : α → Prop} (h : Returns t P) (hPQ : ∀ a, P a → Q a) :
    Returns t Q := by
  have := h.bind (k := pure) (fun a ha => returns_pure.mpr (hPQ a ha))
  rwa [_root_.bind_pure] at this

theorem returns_tau1 {t : Tree α} {P : α → Prop} : Returns (CTree.tau1 t) P ↔ Returns t P := by
  rw [CTree.tau1_def]
  exact (Sim.tau_l _ _ _ _).trans ⟨fun h => h ⟨⟩, fun h _ => h⟩

/-- A tree that chooses a value and then returns only values satisfying `P`, whatever it chose. -/
theorem returns_choose_bind {SubCIn : Type} {SubC : SubCIn → Type} [SubC -< FreezeC]
    (i : SubCIn) {k : SubC i → Tree β} {P : β → Prop} (h : ∀ x, Returns (k x) P) :
    Returns (CTree.choose (E := ErrorE ⊕ₑ UBE) i >>= k) P := by
  rw [CTree.choose_def, CTree.tau_def, bind_tau]
  refine (Sim.tau_l _ _ _ _).mpr fun x => ?_
  rw [CTree.CTree.ret_pure, pure_bind]
  exact h _

theorem Returns.inflate {t : Tree α} {P : α → Prop} (h : Returns t P) : Returns (inflate t) P := by
  show Sim _ (Veir.CTree.inflate t) (pure ())
  rw [← inflate_pure ()]
  exact Sim.interp _ t (pure ()) h

/-- A simulation with a stronger relation. -/
theorem sim_mono {RR RR' : α → β → Prop} {t : Tree α} {s : Tree β} (h : Sim RR t s)
    (hRR : ∀ a b, RR a b → RR' a b) : Sim RR' t s := by
  have := Sim.bind (RR' := RR') t s pure pure h (fun a b hab => (Sim.pure _ _ _).mpr (hRR a b hab))
  rwa [← tree_bind_eq, ← tree_bind_eq, _root_.bind_pure, _root_.bind_pure] at this

/-- A simulation of a source that returns one value, together with what holds of that value. -/
theorem sim_pure_and {RR : α → β → Prop} {t : Tree α} {b : β} (h : Sim RR t (pure b : Tree β))
    {P : β → Prop} (hb : P b) : Sim (fun a b => RR a b ∧ P b) t (pure b : Tree β) := by
  have h₂ : Sim (fun (y z : β) => y = z ∧ P z) (pure b : Tree β) (pure b : Tree β) :=
    (Sim.pure _ _ _).mpr ⟨rfl, hb⟩
  refine sim_mono (Sim.trans_rel h h₂) fun a z ⟨y, h₁, hyz, hz⟩ => ?_
  subst hyz
  exact ⟨h₁, hz⟩

/-- A source step after a target tree that returns only values satisfying `P`. -/
theorem sim_bind_of_returns {RR : β → γ → Prop} {t : Tree α} {P : α → Prop} {k : α → Tree β}
    {s : Tree γ} (h : Returns t P) (hk : ∀ a, P a → Sim RR (k a) s) : Sim RR (t >>= k) s := by
  have := Sim.bind (RR' := RR) t (pure ()) k (fun _ => s) h (fun a _ ha => hk a ha)
  rw [CTree.bind_pure] at this
  rwa [tree_bind_eq]

/-- A target tree that returns only values related to the value the source returns. -/
theorem sim_pure_of_returns {RR : α → γ → Prop} {t : Tree α} {s : γ}
    (h : Returns t (fun a => RR a s)) : Sim RR t (pure s : Tree γ) := by
  have := sim_bind_of_returns (k := pure) (s := (pure s : Tree γ)) h
    (fun a ha => (Sim.pure _ _ _).mpr ha)
  rwa [_root_.bind_pure] at this

/-- A source that is the lift of an `Interp` outcome: only its successful outcome needs a
target. -/
theorem sim_monadLift_bind {RR : β → γ → Prop} {t : Tree β} {outcome : Interp α}
    {k : α → Tree γ} (h : ∀ a, outcome = .ok a → Sim RR t (k a)) :
    Sim RR t (monadLift outcome >>= k) := by
  cases outcome with
  | ok a => simpa [monadLift, MonadLift.monadLift] using h a rfl
  | ub _ => simp [monadLift, MonadLift.monadLift, tree_bind_eq]
  | fail _ => simp [monadLift, MonadLift.monadLift, tree_bind_eq]

/-- A source that is the lift of an `Interp` outcome, without a continuation. -/
theorem sim_monadLift {RR : β → α → Prop} {t : Tree β} {outcome : Interp α}
    (h : ∀ a, outcome = .ok a → Sim RR t (pure a : Tree α)) :
    Sim RR t (monadLift outcome : Tree α) := by
  have := sim_monadLift_bind (k := pure) h
  rwa [_root_.bind_pure] at this

/-- A silent step of the target. -/
theorem sim_tau1_left {RR : α → β → Prop} {t : Tree α} {s : Tree β} (h : Sim RR t s) :
    Sim RR (CTree.tau1 t) s := by
  rw [CTree.tau1_def]
  exact (Sim.tau_l _ _ _ _).mpr fun _ => h

/-- A silent step of the source. -/
theorem sim_tau1_right {RR : α → β → Prop} {t : Tree α} {s : Tree β} (h : Sim RR t s) :
    Sim RR t (CTree.tau1 s) := by
  rw [CTree.tau1_def]
  exact Sim.tau_r _ _ _ _ ⟨⟩ h

/-! ## Lists of operations -/

variable {ctx ctx' : WfIRContext OpCode}

/--
Run a list of operations as a closed tree, stopping at the first terminator, as `interpretOpList`
does. Each operation is one silent step, as in the closed CFG loop.
-/
def opListTree (ops : List OperationPtr) (state : InterpreterState ctx)
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw) : Tree (InterpreterState ctx × Option ControlFlowAction) :=
  match ops with
  | [] => pure (state, none)
  | op :: ops => CTree.tau1 (interpretOperationTree op state (opsIn op (by simp)) >>= fun r =>
    r.2.elim (opListTree ops r.1 (fun op' h => opsIn op' (by simp [h])))
      (fun cf => pure (r.1, some cf)))

@[simp]
theorem opListTree_nil {state : InterpreterState ctx} {opsIn} :
    opListTree [] state opsIn = pure (state, none) := by
  rw [opListTree]

theorem opListTree_cons {op : OperationPtr} {ops : List OperationPtr}
    {state : InterpreterState ctx} {opsIn : ∀ o ∈ op :: ops, o.InBounds ctx.raw} :
    opListTree (op :: ops) state opsIn =
      CTree.tau1 (interpretOperationTree op state (opsIn op (by simp)) >>= fun r =>
        r.2.elim (opListTree ops r.1 (fun op' h => opsIn op' (by simp [h])))
          (fun cf => pure (r.1, some cf))) := by
  rw [opListTree]

/-- What runs after a list of operations that is followed by more operations. -/
abbrev opListCont (ops : List OperationPtr) (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (r : InterpreterState ctx × Option ControlFlowAction) :
    Tree (InterpreterState ctx × Option ControlFlowAction) :=
  r.2.elim (opListTree ops r.1 opsIn) (fun cf => pure (r.1, some cf))

theorem opListTree_append {ops₁ ops₂ : List OperationPtr} {state : InterpreterState ctx}
    {opsIn : ∀ op ∈ ops₁ ++ ops₂, op.InBounds ctx.raw} :
    opListTree (ops₁ ++ ops₂) state opsIn =
      opListTree ops₁ state (fun op h => opsIn op (by simp [h])) >>=
        opListCont ops₂ (fun op h => opsIn op (by simp [h])) := by
  induction ops₁ generalizing state with
  | nil => simp [opListCont]
  | cons op ops₁ ih =>
    simp only [List.cons_append, opListTree_cons, CTree.tau1_def, bind_tau, CTree.bind_assoc]
    congr 1
    funext _
    congr 1
    funext r
    rcases r with ⟨state', _ | cf⟩
    · exact ih
    · simp [opListCont]

theorem opListTree_congr {ops ops' : List OperationPtr} (h : ops = ops')
    {state : InterpreterState ctx} {opsIn : ∀ op ∈ ops, op.InBounds ctx.raw} :
    opListTree ops state opsIn = opListTree ops' state (h ▸ opsIn) := by
  subst h; rfl

/-- Run a list of operations that ends in a terminator, as `interpretTerminatedOpList` does. -/
def terminatedOpListTree (ops : List OperationPtr) (state : InterpreterState ctx)
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw) : Tree (InterpreterState ctx × ControlFlowAction) :=
  opListTree ops state opsIn >>= fun r => r.2.elim fail (fun cf => pure (r.1, cf))

theorem terminatedOpListTree_eq {ops : List OperationPtr} {state : InterpreterState ctx}
    {opsIn : ∀ op ∈ ops, op.InBounds ctx.raw} :
    terminatedOpListTree ops state opsIn =
      opListTree ops state opsIn >>= fun r => r.2.elim fail (fun cf => pure (r.1, cf)) := by
  rw [terminatedOpListTree]

/-! ## A block step runs the operations of the block -/

/-- Where the closed CFG loop goes after the terminator of a block. -/
def finishBlock (r : InterpreterState ctx × ControlFlowAction) :
    Tree (CFGState ctx ⊕ CFGResult ctx) :=
  match r.2 with
  | .return results => pure (.inr (r.1, results))
  | .branch args dest =>
    if h : dest.InBounds ctx.raw then pure (.inl (CFGState.entry h args r.1)) else fail

@[simp]
theorem finishBlock_return {state : InterpreterState ctx} {results : Array RuntimeValue} :
    finishBlock (state, .return results) = pure (.inr (state, results)) := by
  rw [finishBlock]

@[simp]
theorem finishBlock_branch {state : InterpreterState ctx} {args : Array RuntimeValue}
    {dest : BlockPtr} :
    finishBlock (state, .branch args dest) =
      if h : dest.InBounds ctx.raw then pure (.inl (CFGState.entry h args state)) else fail := by
  rw [finishBlock]

/-- The rest of a block from one of its operations runs as the list of the remaining operations. -/
theorem blockStep_atOperation {block : BlockPtr} {array : Array OperationPtr}
    (hChain : BlockPtr.OpChain block ctx.raw array) (n : Nat) :
    ∀ (i : Nat) (state : InterpreterState ctx) (_hn : i + n = array.size) (hi : i < array.size),
      CTree.tau1 (blockStep ((.inr ⟨array[i], hChain.arrayInBounds (Array.getElem_mem hi)⟩,
          state) : CFGState ctx)) =
        terminatedOpListTree (array.toList.drop i) state
          (fun op h => hChain.arrayInBounds (Array.mem_toList_iff.mp (List.mem_of_mem_drop h)))
          >>= finishBlock := by
  induction n with
  | zero => intro i _ hn hi; omega
  | succ n ih =>
    intro i state hn hi
    have hDrop : array.toList.drop i = array[i] :: array.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]
      simp
    have opIn := hChain.arrayInBounds (Array.getElem_mem hi)
    have hNext := hChain.next hi
    rw [OperationPtr.getNextOp!_eq_getNextOp opIn] at hNext
    rw [blockStep, spliceWhile_eq, terminatedOpListTree_eq,
      opListTree_congr hDrop, opListTree_cons]
    simp only [cfgStep, interpretCFGTreeStep, CTree.tau1_def, bind_tau, CTree.bind_assoc]
    congr 1
    funext _
    congr 1
    funext r
    rcases r with ⟨state', _ | (results | ⟨args, dest⟩)⟩
    · simp only [interpretCFGTreeContinue, Option.elim_none]
      by_cases hLast : i + 1 < array.size
      · have hNext' : array[i].getNextOp ctx.raw opIn = some array[i + 1] := by
          rw [hNext]; simp [hLast]
        have := ih (i + 1) state' (by omega) hLast
        rw [blockStep, terminatedOpListTree_eq, CTree.tau1_def] at this
        split
        · next nextOp hEq =>
          rw [hNext'] at hEq
          obtain rfl := Option.some.inj hEq
          simp only [pure_bind, CFGState.atOperation, Sum.isRight_inr, ↓reduceIte]
          rw [this, CTree.bind_assoc]
        · next hNone => exact (hNone _ hNext').elim
      · have hNext' : array[i].getNextOp ctx.raw opIn = none := by
          rw [hNext]; simp [hLast]
        have hEmpty : array.toList.drop (i + 1) = [] := by simp; omega
        rw [opListTree_congr hEmpty]
        split
        · next nextOp hEq => rw [hNext'] at hEq; cases hEq
        · simp
    · simp [interpretCFGTreeContinue, finishBlock]
    · simp only [interpretCFGTreeContinue, finishBlock, pure_bind, Option.elim_some]
      split <;> simp [CFGState.atOperation, CFGState.entry]

/-- A block step sets the arguments of the block and runs the list of its operations. -/
theorem blockStep_entry {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (values : Array RuntimeValue) (state : InterpreterState ctx) :
    blockStep (CFGState.entry blockIn values state) =
      if values.size != block.getNumArguments ctx.raw then fail else
      match state.variables.setArgumentValues? block values blockIn with
      | none => fail
      | some variables =>
        terminatedOpListTree (block.operationList ctx.raw ctx.wellFormed blockIn).toList
          ⟨variables, state.memory⟩ (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]) >>=
          finishBlock := by
  have hChain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  have hFirstEq := hChain.first
  rw [BlockPtr.getFirstOp!_eq_getFirstOp blockIn] at hFirstEq
  rw [blockStep, spliceWhile_eq]
  simp only [cfgStep, CFGState.entry, interpretCFGTreeStep]
  by_cases hSize : (values.size != block.getNumArguments ctx.raw) = true
  · simp [hSize]
  simp only [hSize, Bool.false_eq_true, ↓reduceIte]
  rcases hSet : state.variables.setArgumentValues? block values blockIn with _ | variables
  · simp
  simp only
  split
  · next firstOp hFirst =>
    rw [hFirst] at hFirstEq
    obtain ⟨h0, hFirst'⟩ := Array.getElem?_eq_some_iff.mp hFirstEq.symm
    have := blockStep_atOperation hChain (block.operationList ctx.raw ctx.wellFormed blockIn).size 0
      ⟨variables, state.memory⟩ (by omega) h0
    simp only [List.drop_zero] at this
    simp only [pure_bind, CFGState.atOperation, Sum.isRight_inr, ↓reduceIte]
    subst hFirst'
    rw [← this, blockStep]
  · next hNone =>
    have hEmpty : (block.operationList ctx.raw ctx.wellFormed blockIn).toList = [] := by
      rcases h : (block.operationList ctx.raw ctx.wellFormed blockIn)[0]? with _ | firstOp
      · simpa using h
      · rw [h] at hFirstEq; exact (hNone _ hFirstEq).elim
    rw [terminatedOpListTree_eq, opListTree_congr hEmpty]
    simp

/-! ## An operation that a transformation keeps -/

/-- The closed tree of an operation, with the getters that `interpretOp` uses. -/
theorem interpretOperationTree_eq {op : OperationPtr} (state : InterpreterState ctx)
    (opIn : op.InBounds ctx.raw) :
    interpretOperationTree op state opIn = do
      let some operands := state.variables.getOperandValues op | fail
      let (resultValues, mem, action) ← inflate (inflate (interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw) operands
        (op.getSuccessors! ctx.raw) state.memory))
      let some variables := state.variables.setResultValues? op resultValues opIn | fail
      return (⟨variables, mem⟩, action) := by
  have hOp : ∀ operands, interpretOp' (op.getOpType ctx.raw opIn)
      (op.getProperties ctx.raw (op.getOpType ctx.raw opIn)) (op.getResultTypes ctx.raw) operands
      (op.getSuccessors ctx.raw) state.memory (op.getRegions ctx.raw) =
      interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw) operands
        (op.getSuccessors! ctx.raw) state.memory := by
    intro operands
    rw [interpretOp'_regions]
    congr 1 <;> grind
  simp only [interpretOperationTree, hOp]
  rfl

/-- `interpretOp'` of an opcode is that of an equal opcode, with the properties carried over. -/
theorem interpretOp'_opType_cast {opType opType' : OpCode} {properties : propertiesOf opType}
    {properties' : propertiesOf opType'} (hType : opType = opType')
    (hProperties : properties = hType ▸ properties') (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState) :
    interpretOp' opType properties resultTypes operands blockOperands mem =
      interpretOp' opType' properties' resultTypes operands blockOperands mem := by
  subst hType hProperties
  rfl

/--
An operation is monotone in CTrees, in its operands and its memory, on operands that conform to
its operand types: running it on refined operands and refined memory has only behaviors that it
has on the original ones, up to refinement of the results and of the memory.
-/
@[expose]
def _root_.Veir.OperationPtr.TreeMonotone (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  ∀ (operands operands' : Array RuntimeValue) (mem mem' : MemoryState),
    RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw) →
    operands ⊒ operands' → mem ⊒ mem' →
    Sim (fun t s => OperationResult.isRefinedBy s t)
      (interpretOp' (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) operands' (op.getSuccessors! ctx.raw) mem')
      (interpretOp' (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) mem)

/-- An operation whose opcode is monotone in CTrees is. -/
theorem _root_.Veir.OperationPtr.treeMonotone_of_interpretOpTreeMonotone {op : OperationPtr}
    [inst : InterpretOpTreeMonotone (op.getOpType! ctx.raw)] : op.TreeMonotone ctx :=
  fun operands operands' mem mem' _ h hMem =>
    inst.monotone _ _ operands operands' _ mem mem' #[] h hMem

/-- An operation that verifies is monotone in CTrees if its opcode meets its CTree obligation. -/
theorem _root_.Veir.OperationPtr.treeMonotone_of_interpretCTree_monotone {op : OperationPtr}
    (opIn : op.InBounds ctx.raw) (hVerified : op.Verified ctx opIn)
    (hMono : (op.getOpType! ctx.raw).interpretCTree_monotone) : op.TreeMonotone ctx := by
  intro operands operands' mem mem' hConforms h hMem
  have := hMono ctx op opIn (OperationPtr.getOpType!_eq_getOpType opIn).symm hVerified operands
    operands' mem mem' hConforms h hMem
  rw [OperationPtr.interpretCTree_eq, OperationPtr.interpretCTree_eq] at this
  exact sim_mono this fun _ _ h => h.1

/--
An operation that a value mapping preserves, run on related states, has only behaviors that it
has in the source, with related states and actions. The source state is the one in which the
results of the operation are set.
-/
theorem interpretOperationTree_sim_of_preservesOperation
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'} {op op' : OperationPtr}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hMono : op.TreeMonotone ctx)
    (hState : state.isRefinedBy state' mapping)
    (hPreserves : mapping.PreservesOperation op op') :
    Sim (fun (t : InterpreterState ctx' × Option ControlFlowAction)
        (s : InterpreterState ctx × Option ControlFlowAction) =>
        s.1.isRefinedBy t.1 mapping ∧ ControlFlowAction.optionIsRefinedBy s.2 t.2 ∧
        (∃ results, state.variables.setResultValues? op results opIn = some s.1.variables) ∧
        ((op.getOpType! ctx.raw).isLifted = false → s.2 = none))
      (interpretOperationTree op' state' opIn') (interpretOperationTree op state opIn) := by
  rw [interpretOperationTree_eq, interpretOperationTree_eq]
  obtain ⟨hMem, hVars⟩ := hState
  rcases hSrcOps : state.variables.getOperandValues op with _ | operands
  · simp
  obtain ⟨operands', hTgtOps, hOpsRef⟩ :=
    VariableState.getOperandValues_isRefinedBy hVars opIn hPreserves.operands hSrcOps
  simp only [hTgtOps]
  rw [interpretOp'_opType_cast hPreserves.opType hPreserves.props, hPreserves.resultTypes,
    hPreserves.successors, tree_bind_eq, tree_bind_eq]
  apply Sim.bind (RR := fun t s => OperationResult.isRefinedBy s t ∧
    ((op.getOpType! ctx.raw).isLifted = false → s.2.2 = none))
  · apply Sim.interp
    apply Sim.interp
    have := hMono operands operands' state.memory state'.memory
      (VariableState.getOperandValues_conforms hSrcOps) hOpsRef hMem
    cases hLifted : (op.getOpType! ctx.raw).isLifted
    · rw [← interpretOp'_bind_dropAction hLifted _ _ operands,
        ← interpretOp'_bind_dropAction hLifted _ _ operands', tree_bind_eq, tree_bind_eq]
      refine Sim.bind _ _ _ _ this fun t s hts => ?_
      obtain ⟨h₁, h₂, -⟩ := hts
      exact (Sim.pure _ _ _).mpr ⟨⟨h₁, h₂, by simp [ControlFlowAction.optionIsRefinedBy]⟩,
        fun _ => rfl⟩
    · exact sim_mono this fun t s hts => ⟨hts, fun h => nomatch h⟩
  · rintro ⟨results', mem', action'⟩ ⟨results, mem, action⟩ ⟨hRel, hNone⟩
    obtain ⟨hResults, hMem', hAction⟩ := hRel
    simp only at hResults hMem' hAction hNone ⊢
    rcases hSet : state.variables.setResultValues? op results opIn with _ | variables
    · simp
    have hConforms : RuntimeValue.ArrayConforms results' (op'.getResultTypes! ctx'.raw) := by
      rw [hPreserves.resultTypes]
      exact (RuntimeValue.ArrayConforms_of_setResultValues?_eq_some hSet).of_isRefinedBy hResults
    obtain ⟨variables', hSet', hRefined⟩ := VariableState.setResultValues?_isRefinedBy hVars
      hResults hPreserves.results hPreserves.reflect hSet hConforms opIn'
    simp only [hSet', Sim.pure]
    exact ⟨⟨hMem', hRefined⟩, hAction, ⟨results, hSet⟩, hNone⟩

end Veir.CTree
