module

public import Veir.Buffered.IR.Buffed.SimDefs
public import Veir.Buffered.IR.Buffed.ArgumentFlattening
public import Lean

public section

register_grind_attr generic_ptr_grind
register_grind_attr inbounds

attribute [grind .] Option.ne_none_iff_isSome Option.some_get!

@[grind .]
theorem Option.maybe₁_and_isSome {α} [Inhabited α] (x : Option α) (P : α → Prop) :
    x.maybe₁ P → x.isSome → P x.get! := by
  cases x <;> grind

@[grind .]
theorem Option.maybe_and_isSome_get! {α} [Inhabited α] (x : Option α) (P : α → β → Prop) :
    x.maybe P y → x.isSome → P x.get! y := by
  cases x <;> grind

theorem Veir.Buffered.Sim.IRContext.option_ext [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
    [HasBuffedOpCode OpInfo] (x y : Option (Veir.Buffered.Sim.IRContext OpInfo)) :
    (x.map (·.spec) = y.map (·.spec) ∧ x.map (·.buf) = y.map (·.buf)) → x = y := by
  cases x with
  | none => cases y <;> simp
  | some x =>
    cases y with
    | none => simp
    | some y =>
      simp only [Option.map_some, Option.some.injEq]
      rintro ⟨hspec, hbuf⟩
      cases x
      cases y
      have hs := Erased.out_inj hspec
      cases hs
      cases hbuf
      rfl
