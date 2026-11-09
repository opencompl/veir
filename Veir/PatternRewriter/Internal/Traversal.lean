module

public import Veir.PatternRewriter.Basic
public import Veir.IRNesting
import all Veir.PatternRewriter.Basic
import all Veir.IR.WellFormed
import all Veir.IRNesting

namespace Veir.PatternRewriter
variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Every occupied stack slot satisfies the candidate predicate. -/
@[expose] public def Worklist.All (w : Worklist) (P : OperationPtr → Prop) : Prop :=
  ∀ op, some op ∈ w.stack → P op

public theorem Worklist.all_empty {P : OperationPtr → Prop} : Worklist.empty.All P := by
  simp [Worklist.All, Worklist.empty]

/-- A traversal starting in scope preserves the accumulator invariant whenever it returns. -/
private def FoldPreserves {α σ : Type} (P : σ → Prop) (scope : α → Prop)
    (walk : α → σ → Option σ) : Prop :=
  ∀ x s, scope x → P s → ∀ t, walk x s = some t → P t

private theorem FoldPreserves.admissible {α σ : Type} (P : σ → Prop) (scope : α → Prop) :
    Lean.Order.admissible (FoldPreserves P scope) := by
  apply Lean.Order.admissible_pi_apply (fun (x : α) (f : σ → Option σ) =>
    ∀ s, scope x → P s → ∀ t, f s = some t → P t)
  intro x
  apply Lean.Order.admissible_pi_apply (fun s (result : Option σ) =>
    scope x → P s → ∀ t, result = some t → P t)
  intro s
  exact Lean.Order.admissible_pi _ (fun _ => Lean.Order.admissible_pi _ (fun _ =>
    Lean.Order.admissible_pi _ (fun t => Lean.Order.Option.admissible_eq_some (P t) t)))

private theorem walkRegions_preserves {σ : Type} (ctx : WfIRContext OpInfo) (root : OperationPtr)
    (reverse : Bool) (visit : σ → OperationPtr → σ × Bool) (P : σ → Prop)
    (step : ∀ s (op : OperationPtr), P s → op.InBounds ctx.raw → root.Ancestor op ctx → P (visit s op).1) :
    ∀ op : OperationPtr, FoldPreserves P
      (fun n => op.InBounds ctx.raw ∧ root.Ancestor op ctx ∧ n ≤ op.getNumRegions! ctx.raw)
      (walkRegions ctx.raw reverse visit op) := by
  let blocks (next : Option BlockPtr) := ∀ b, next = some b → ∃ r : RegionPtr,
    r.InBounds ctx.raw ∧ root.Ancestor r ctx ∧ b.InBounds ctx.raw ∧ b.getParent! ctx.raw = some r
  let operations (next : Option OperationPtr) := ∀ op, next = some op → ∃ b : BlockPtr,
    b.InBounds ctx.raw ∧ root.Ancestor b ctx ∧ op.InBounds ctx.raw ∧ op.getParent! ctx.raw = some b
  apply walkRegions.fixpoint_induct ctx.raw reverse visit
    (fun walk => ∀ op : OperationPtr, FoldPreserves P
      (fun n => op.InBounds ctx.raw ∧ root.Ancestor op ctx ∧ n ≤ op.getNumRegions! ctx.raw) (walk op))
    (FoldPreserves P blocks) (FoldPreserves P operations)
  · exact Lean.Order.admissible_pi_apply _ (fun _ => FoldPreserves.admissible P _)
  · exact FoldPreserves.admissible P blocks
  · exact FoldPreserves.admissible P operations
  · intro regions blocks' ihRegions ihBlocks op n s scope hs t run
    obtain ⟨inside, ancestry, bound⟩ := scope
    cases n with
    | zero => cases run; exact hs
    | succ n =>
      obtain ⟨mid, visited, rest⟩ := Option.bind_eq_some_iff.mp run
      apply ihRegions op n mid ⟨inside, ancestry, by omega⟩ _ t rest
      apply ihBlocks _ s _ hs _ visited
      let j := if reverse then n else op.getNumRegions! ctx.raw - (n + 1)
      have hj : j < op.getNumRegions! ctx.raw := by unfold j; split <;> omega
      let r := op.getRegion! ctx.raw j
      have rin : r.InBounds ctx.raw := by dsimp [r]; grind
      have rp := ((ctx.wellFormed.operations op inside).region_parent r rin).mp ⟨j, hj, rfl⟩
      have ra : root.Ancestor r ctx := ancestry.of_ancestor_parent_of_parent_descendant (by grind)
      intro b found
      exact ⟨r, rin, ra, by split at found <;> grind, by split at found <;> grind⟩
  · intro blocks' ops ihBlocks ihOps next s scope hs t run
    cases next with
    | none => cases run; exact hs
    | some b =>
      obtain ⟨r, rin, ra, bin, bp⟩ := scope b rfl
      have ba : root.Ancestor b ctx := ra.of_ancestor_parent_of_parent_descendant (by grind)
      obtain ⟨mid, visited, rest⟩ := Option.bind_eq_some_iff.mp run
      apply ihBlocks _ mid _ _ t rest
      · intro next found
        exact ⟨r, rin, ra, by split at found <;> grind, by split at found <;> grind⟩
      · apply ihOps _ s _ hs _ visited
        intro child found
        exact ⟨b, bin, ba, by split at found <;> grind, by split at found <;> grind⟩
  · intro regions ops ihRegions ihOps next s scope hs t run
    cases next with
    | none => cases run; exact hs
    | some op =>
      obtain ⟨b, bin, ba, inside, parent⟩ := scope op rfl
      have chain := BlockPtr.operationListWF ctx.raw b bin ctx.wellFormed
      have nested : root.Ancestor op ctx := ba.of_ancestor_parent_of_parent_descendant (by grind)
      have post := step s op hs inside nested
      have siblings : operations (if reverse then op.getPrevOp! ctx.raw else op.getNextOp! ctx.raw) := by
        intro sibling found
        exact ⟨b, bin, ba, by split at found <;> grind, by split at found <;> grind⟩
      cases visited : visit s op with
      | mk acc descend =>
        cases descend <;> simp only [visited, Bool.false_eq_true, ↓reduceIte] at run post
        · exact ihOps _ acc siblings post t run
        · obtain ⟨mid, children, rest⟩ := Option.bind_eq_some_iff.mp run
          exact ihOps _ mid siblings (ihRegions op _ acc ⟨inside, nested, Nat.le_refl _⟩ post mid children) t rest

private theorem foldNestedOperations_preserves {σ : Type} (ctx : WfIRContext OpInfo)
    (root : OperationPtr) (reverse : Bool)
    (visit : σ → OperationPtr → σ × Bool) (P : σ → Prop)
    (step : ∀ s (op : OperationPtr), P s → op.InBounds ctx.raw → root.Ancestor op ctx → P (visit s op).1)
    (s : σ) (hs : P s) : P (foldNestedOperations ctx.raw root reverse visit s) := by
  unfold foldNestedOperations
  split <;> rename_i inside
  case isFalse => exact hs
  cases run : walkRegions ctx.raw reverse visit root (root.getNumRegions! ctx.raw) s with
  | none => exact hs
  | some t =>
    exact walkRegions_preserves ctx root reverse visit P step root _ s ⟨inside, .refl, Nat.le_refl _⟩ hs t run

private theorem seedNestedReversePostOrder_all (ctx : WfIRContext OpInfo)
    (root : OperationPtr) :
    (seedNestedReversePostOrder ctx.raw .empty root).All (fun op => root.Ancestor op ctx) := by
  unfold seedNestedReversePostOrder
  refine foldNestedOperations_preserves ctx root true _
    (fun (w : Worklist) => w.All (fun op => root.Ancestor op ctx)) ?_ _ Worklist.all_empty
  intro w child all _ nested op mem
  change some op ∈ w.stack.push (some child) at mem
  rcases Array.mem_push.mp mem with old | eq
  · exact all _ old
  · cases eq; exact nested

public theorem collectNestedFunctions_scoped (ctx : WfIRContext OpInfo) (root : OperationPtr) :
    ∀ f ∈ collectNestedFunctions ctx.raw root (includeDeclarations := false),
      f.InBounds ctx.raw ∧ 0 < f.getNumRegions! ctx.raw ∧ root.Ancestor f ctx := by
  unfold collectNestedFunctions
  refine foldNestedOperations_preserves ctx root false _
    (fun (fs : Array OperationPtr) => ∀ f ∈ fs,
      f.InBounds ctx.raw ∧ 0 < f.getNumRegions! ctx.raw ∧ root.Ancestor f ctx) ?_ #[] ?_
  · intro fs child all cin nested
    split
    · dsimp only
      split
      next body =>
        intro f mem
        rcases Array.mem_push.mp mem with old | rfl
        · exact all f old
        · exact ⟨cin, by simpa using body, nested⟩
      next => exact all
    · exact all
  · simp

end Veir.PatternRewriter
