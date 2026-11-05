module

public import Veir.Data.Tensor
public import Veir.IR.AffineMap

/-!
  # A reference model of `linalg.generic`

  This file gives a pure model of `linalg.generic` on tensors, polymorphic in the
  element type `α`, which all operands share. An interpreter instantiates `α` with its
  runtime values.

  ## Tensors

  Operands are modelled by `Veir.Data.Tensor`. A scalar operand is a rank-0 tensor,
  and its indexing map has no results, as in MLIR.

  ## Semantics

  `generic maps numInputs bounds body operands` iterates over the loop space `bounds`
  in lexicographic order. At every point `idx` it reads, for every operand `k`, the
  element of `operands[k]` at `maps[k](idx)`. Outputs are read from their current,
  partially updated value, which is what makes reductions work. It then applies `body`
  to `idx`, which `linalg.index` reads, and to these elements, and writes result `j`
  into output `j`, which is operand `numInputs + j`, at `maps[numInputs + j](idx)`.
  Finally, it returns the outputs.

  ## Out-of-bounds accesses

  The model is total, but only meaningful if `AccessesInBounds` holds: an access
  outside the shape of an operand reads an element that `Tensor.Rel` ignores. The
  verifier does not ensure this, since, as in MLIR, it does not check operand
  dimensions of size 0, so an interpreter has to check it.
  ## Relating runs

  `generic_rel` relates two runs whose operands and bodies are related by a relation
  `r` on the elements, such as equality or refinement, and `genericM_option_rel` does
  so for bodies that can fail.
-/

namespace Veir.Linalg.Model

open Veir.Data

public section

/-! ## The loop nest -/

/--
  Evaluate an affine expression at the loop index `idx`. This is an `Int`, so that a
  negative index is out of bounds rather than truncated to 0.
-/
@[expose]
def evalExpr (idx : List Nat) : AffineExpr n → Int
  | .dim i => idx[i.val]?.getD 0
  | .const c => c

/-- Evaluate an affine map at the loop index `idx`. -/
@[expose]
def evalMap (map : AffineMapAttr) (idx : List Nat) : List Int :=
  map.results.toList.map (evalExpr idx)

/--
  The tensor index that `map` accesses at the loop index `idx`. A negative entry
  becomes 0, which `AccessesInBounds` rules out.
-/
@[expose]
def access (map : AffineMapAttr) (idx : List Nat) : List Nat :=
  (evalMap map idx).map Int.toNat

/-- The block arguments at the loop index `idx`, one per operand. -/
@[expose]
def readArgs (maps : Array AffineMapAttr) (operands : Array (Tensor α)) (idx : List Nat) :
    Array α :=
  operands.mapIdx fun k t => t.get (access maps[k]! idx)

/--
  Write the yielded values `results` at the loop index `idx` into the outputs, which
  are the operands from `numInputs` on.
-/
@[expose]
def writeResults (maps : Array AffineMapAttr) (numInputs : Nat)
    (operands : Array (Tensor α)) (idx : List Nat) (results : Array α) :
    Array (Tensor α) :=
  operands.mapIdx fun k t =>
    if numInputs ≤ k then
      match results[k - numInputs]? with
      | some v => t.set (access maps[k]! idx) v
      | none => t
    else t

/--
  The `linalg.generic` loop nest, with a monadic body, e.g. one that interprets the
  region of the operation.

  * `maps`: one indexing map per operand;
  * `numInputs`: the number of inputs, the remaining operands are outputs;
  * `bounds`: the size of every loop;
  * `body`: maps the loop index and the block arguments (one per operand) to the
    yielded values (one per output);
  * `operands`: the inputs followed by the outputs.

  Returns the final value of every output.
-/
@[expose]
def genericM [Monad m] (maps : Array AffineMapAttr) (numInputs : Nat) (bounds : List Nat)
    (body : List Nat → Array α → m (Array α)) (operands : Array (Tensor α)) :
    m (Array (Tensor α)) := do
  let final ← (Tensor.indices bounds).foldlM (init := operands) fun operands idx => do
    let results ← body idx (readArgs maps operands idx)
    pure (writeResults maps numInputs operands idx results)
  pure (final.extract numInputs)

/-- `linalg.generic` with a pure body, see `genericM`. -/
@[expose]
def generic (maps : Array AffineMapAttr) (numInputs : Nat) (bounds : List Nat)
    (body : List Nat → Array α → Array α) (operands : Array (Tensor α)) : Array (Tensor α) :=
  Id.run (genericM maps numInputs bounds (fun idx args => pure (body idx args)) operands)

/-! ## Accesses within bounds -/

/-- `i` is an index within `shape`, with no negative entries. -/
@[expose]
def IndexInBounds (i : List Int) (shape : List Nat) : Prop :=
  (∀ x ∈ i, 0 ≤ x) ∧ Tensor.InBounds (i.map Int.toNat) shape

instance : Decidable (IndexInBounds i shape) :=
  inferInstanceAs (Decidable (_ ∧ _))

/--
  At every point of the loop space `bounds`, every operand is accessed within its
  shape, given in `shapes`. This only depends on the shapes, so that an interpreter can
  check it before running the loop nest.
-/
@[expose]
def AccessesInBounds (maps : Array AffineMapAttr) (bounds : List Nat)
    (shapes : Array (List Nat)) : Prop :=
  ∀ idx ∈ Tensor.indices bounds, ∀ k (h : k < shapes.size),
    IndexInBounds (evalMap maps[k]! idx) shapes[k]

instance : Decidable (AccessesInBounds maps bounds shapes) := by
  unfold AccessesInBounds
  infer_instance

/-! ## Relating runs of the loop nest -/

/--
  Arrays of values, such as the block arguments or the yielded values of the body,
  that have the same size and are related by `r` pointwise.
-/
@[expose]
def ValuesRel (r : α → β → Prop) (vs : Array α) (ws : Array β) : Prop :=
  vs.size = ws.size ∧ ∀ k (h : k < vs.size) (h' : k < ws.size), r vs[k] ws[k]

/--
  Arrays of operands that have the same size and are related by `Tensor.Rel r`
  pointwise. For example, `OperandsRel Eq` is equivalence, and `OperandsRel` of the
  refinement of the elements is the refinement of operands.
-/
@[expose]
def OperandsRel (r : α → β → Prop) (operands : Array (Tensor α))
    (operands' : Array (Tensor β)) : Prop :=
  operands.size = operands'.size ∧
    ∀ k (h : k < operands.size) (h' : k < operands'.size), operands[k].Rel r operands'[k]

/-- Pointwise equivalent operands. -/
abbrev OperandsEquiv : Array (Tensor α) → Array (Tensor α) → Prop :=
  OperandsRel Eq

theorem OperandsRel.extract {operands : Array (Tensor α)} {operands' : Array (Tensor β)}
    (h : OperandsRel r operands operands') (start : Nat) :
    OperandsRel r (operands.extract start) (operands'.extract start) :=
  ⟨by simp [h.1], fun k hk hk' => by
    simp only [Array.getElem_extract]
    exact h.2 _ _ _⟩

/-- The `r`-related operands give `r`-related block arguments, if read within bounds. -/
private theorem readArgs_rel {operands : Array (Tensor α)} {operands' : Array (Tensor β)}
    (h : OperandsRel r operands operands')
    (hb : ∀ k (hk : k < operands.size),
      IndexInBounds (evalMap maps[k]! idx) operands[k].shape) :
    ValuesRel r (readArgs maps operands idx) (readArgs maps operands' idx) := by
  refine ⟨by simp [readArgs, h.1], fun k hk hk' => ?_⟩
  simp only [readArgs, Array.size_mapIdx] at hk hk'
  simp only [readArgs, Array.getElem_mapIdx]
  exact (h.2 k hk hk').2 _ (hb k hk).2

private theorem writeResults_rel {operands : Array (Tensor α)} {operands' : Array (Tensor β)}
    (h : OperandsRel r operands operands') (hr : ValuesRel r results results') :
    OperandsRel r (writeResults maps numInputs operands idx results)
      (writeResults maps numInputs operands' idx results') := by
  refine ⟨by simp [writeResults, h.1], fun k hk hk' => ?_⟩
  simp only [writeResults, Array.size_mapIdx] at hk hk'
  simp only [writeResults, Array.getElem_mapIdx]
  have := h.2 k hk hk'
  split
  · by_cases hj : k - numInputs < results.size
    · simp only [Array.getElem?_eq_getElem hj, Array.getElem?_eq_getElem (hr.1 ▸ hj)]
      exact Tensor.Rel.set this _ (hr.2 _ _ _)
    · simp only [Array.getElem?_eq_none (Nat.le_of_not_lt hj),
        Array.getElem?_eq_none (hr.1 ▸ Nat.le_of_not_lt hj)]
      exact this
  · exact this

private theorem shape_writeResults {operands : Array (Tensor α)}
    (hk : k < (writeResults maps numInputs operands idx results).size) :
    (writeResults maps numInputs operands idx results)[k].shape =
      (operands[k]'(by simpa [writeResults] using hk)).shape := by
  simp only [writeResults, Array.getElem_mapIdx]
  split
  · split <;> rfl
  · rfl

/-- The accesses at the loop indices `l` are within the shapes of `operands`. -/
private abbrev LoopInBounds (maps : Array AffineMapAttr) (l : List (List Nat))
    (operands : Array (Tensor α)) : Prop :=
  ∀ idx ∈ l, ∀ k (hk : k < operands.size),
    IndexInBounds (evalMap maps[k]! idx) operands[k].shape

/-- Writing the results keeps the accesses at the remaining loop indices in bounds. -/
private theorem LoopInBounds.tail {operands : Array (Tensor α)}
    (hb : LoopInBounds maps (idx :: l) operands) (results : Array α) :
    LoopInBounds maps l (writeResults maps numInputs operands idx results) :=
  fun idx' hidx' k hk => by
    rw [shape_writeResults]
    exact hb idx' (by simp [hidx']) k _

private theorem loopInBounds_of_accessesInBounds {operands : Array (Tensor α)}
    (hb : AccessesInBounds maps bounds (operands.map (·.shape))) :
    LoopInBounds maps (Tensor.indices bounds) operands := fun idx hidx k hk => by
  have := hb idx hidx k (by simpa using hk)
  rwa [Array.getElem_map] at this

private theorem foldl_rel {l : List (List Nat)} {body : List Nat → Array α → Array α}
    {body' : List Nat → Array β → Array β}
    {operands : Array (Tensor α)} {operands' : Array (Tensor β)}
    (hbody : ∀ idx ∈ l, ∀ args args', ValuesRel r args args' →
      ValuesRel r (body idx args) (body' idx args'))
    (h : OperandsRel r operands operands') (hb : LoopInBounds maps l operands) :
    OperandsRel r
      (l.foldl (fun ops idx => writeResults maps numInputs ops idx
        (body idx (readArgs maps ops idx))) operands)
      (l.foldl (fun ops idx => writeResults maps numInputs ops idx
        (body' idx (readArgs maps ops idx))) operands') := by
  induction l generalizing operands operands' with
  | nil => exact h
  | cons idx l ih =>
    refine ih (fun idx' h' => hbody idx' (by simp [h'])) ?_ (hb.tail _)
    exact writeResults_rel h
      (hbody idx (by simp) _ _ (readArgs_rel h (hb idx (by simp))))

/--
  `generic` maps `r`-related operands to `r`-related outputs, provided that all
  accesses are within the shapes of the source operands, and that the bodies map
  `r`-related block arguments to `r`-related yielded values at every loop index.

  The bodies may differ, e.g. to show that a rewrite of the body refines it.
-/
theorem generic_rel {operands : Array (Tensor α)} {operands' : Array (Tensor β)}
    {body : List Nat → Array α → Array α} {body' : List Nat → Array β → Array β}
    (hbody : ∀ idx ∈ Tensor.indices bounds, ∀ args args', ValuesRel r args args' →
      ValuesRel r (body idx args) (body' idx args'))
    (h : OperandsRel r operands operands')
    (hb : AccessesInBounds maps bounds (operands.map (·.shape))) :
    OperandsRel r (generic maps numInputs bounds body operands)
      (generic maps numInputs bounds body' operands') := by
  simp only [generic, genericM, Id.run, List.foldlM_pure, bind_pure_comp, map_pure]
  exact (foldl_rel hbody h (loopInBounds_of_accessesInBounds hb)).extract numInputs

/--
  `generic` maps equivalent operands to equivalent outputs, provided that all accesses
  are within bounds.
-/
theorem generic_equiv {operands operands' : Array (Tensor α)}
    (h : OperandsEquiv operands operands')
    (hb : AccessesInBounds maps bounds (operands.map (·.shape))) :
    OperandsEquiv (generic maps numInputs bounds body operands)
      (generic maps numInputs bounds body operands') :=
  generic_rel (fun idx _ args args' hargs => by
    obtain rfl : args = args' := Array.ext hargs.1 hargs.2
    exact ⟨rfl, fun _ _ _ => rfl⟩) h hb

/-! ## Relating runs with a failing body -/

private theorem foldlM_rel {l : List (List Nat)} {body : List Nat → Array α → Option (Array α)}
    {body' : List Nat → Array β → Option (Array β)}
    {operands : Array (Tensor α)} {operands' : Array (Tensor β)}
    (hbody : ∀ idx ∈ l, ∀ args args' results, ValuesRel r args args' →
      body idx args = some results →
      ∃ results', body' idx args' = some results' ∧ ValuesRel r results results')
    (h : OperandsRel r operands operands') (hb : LoopInBounds maps l operands)
    (hsome : l.foldlM (fun ops idx => do
        let results ← body idx (readArgs maps ops idx)
        pure (writeResults maps numInputs ops idx results)) operands = some final) :
    ∃ final', l.foldlM (fun ops idx => do
        let results ← body' idx (readArgs maps ops idx)
        pure (writeResults maps numInputs ops idx results)) operands' = some final' ∧
      OperandsRel r final final' := by
  induction l generalizing operands operands' with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hsome
    exact ⟨operands', rfl, hsome ▸ h⟩
  | cons idx l ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.pure_def] at hsome ⊢
    cases hres : body idx (readArgs maps operands idx) with
    | none => simp [hres] at hsome
    | some results =>
      obtain ⟨results', hres', hr⟩ := hbody idx (by simp) _ _ _
        (readArgs_rel h (hb idx (by simp))) hres
      simp only [hres, Option.bind_some, hres'] at hsome ⊢
      exact ih (fun idx' h' => hbody idx' (by simp [h'])) (writeResults_rel h hr)
        (hb.tail _) hsome

/--
  `genericM` in `Option` refines its runs: if it succeeds on `operands`, then it
  succeeds on `r`-related operands, with `r`-related outputs, provided that all accesses
  are within the shapes of `operands`, and that `body'` succeeds with `r`-related
  yielded values on `r`-related block arguments wherever `body` succeeds.
-/
theorem genericM_option_rel {operands : Array (Tensor α)} {operands' : Array (Tensor β)}
    {body : List Nat → Array α → Option (Array α)}
    {body' : List Nat → Array β → Option (Array β)}
    (hbody : ∀ idx ∈ Tensor.indices bounds, ∀ args args' results, ValuesRel r args args' →
      body idx args = some results →
      ∃ results', body' idx args' = some results' ∧ ValuesRel r results results')
    (h : OperandsRel r operands operands')
    (hb : AccessesInBounds maps bounds (operands.map (·.shape)))
    (hsome : genericM maps numInputs bounds body operands = some outputs) :
    ∃ outputs', genericM maps numInputs bounds body' operands' = some outputs' ∧
      OperandsRel r outputs outputs' := by
  unfold genericM at hsome ⊢
  cases hfold : (Tensor.indices bounds).foldlM (fun ops idx => do
      let results ← body idx (readArgs maps ops idx)
      pure (writeResults maps numInputs ops idx results)) operands with
  | none => rw [hfold] at hsome; cases hsome
  | some final =>
    rw [hfold] at hsome
    cases hsome
    obtain ⟨final', hfold', hr⟩ :=
      foldlM_rel hbody h (loopInBounds_of_accessesInBounds hb) hfold
    exact ⟨_, by rw [hfold']; rfl, hr.extract numInputs⟩

end

end Veir.Linalg.Model
