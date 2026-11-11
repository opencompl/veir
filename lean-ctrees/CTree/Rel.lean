module

public import CTree.Order

public section

open Tower Lean.Order

variable {α : Type u} {β : Type v} (R R' : α → α → Prop)

inductive Star : α → α → Prop where
| base a : Star a a
| iter a b c : R a b → Star b c → Star a c

attribute [simp, grind .] Star.base

@[expose]
def Dot (R : α → β → Prop) (R' : β → γ → Prop) x z := ∃ y, R x y ∧ R' y z

abbrev Plus := (Dot R (Star R))

infix:90 "∘" => Dot

postfix:max "^*" => Star

postfix:max "^+" => Plus

theorem Plus.def : Plus R = Dot R (Star R) := by
  rfl

instance Dot.assoc :
    Std.Associative (@Dot α α α) := by
  constructor
  intros R R' R''
  funext x y
  simp [Dot]
  grind

theorem Star.trans (R : α → α → Prop) (hxy : R^* x y) (hyz : R^* y z) :
    R^* x z := by
  induction hxy
  case base y =>
    apply hyz
  case iter x x' y Rxx' Rxy h =>
    apply Star.iter (b := x') <;> grind

theorem Star.trans' (R : α → α → Prop) :
    R^* = R^* ∘ R^* := by
  funext x y
  apply PartialOrder.rel_antisymm
  · simp only [PartialOrder.rel]
    intros h
    exists x
    grind
  · simp only [PartialOrder.rel]
    intros h
    rcases h with ⟨z, hl, hr⟩
    apply Star.trans (y := z) <;> grind

@[grind .]
theorem Star.once : R x y → R^* x y := by
  intros h
  right
  apply h
  left

@[grind .]
theorem Star.skip_l : R' x y → (R^*∘R') x y := by
  intros h
  exists x
  grind

theorem Star.unfold_l (R : α → α → Prop) :
    (R ∘ R^*) x z →
    R^* x z := by
  intro h
  rcases h with ⟨y, h, h'⟩
  apply Star.iter <;> assumption

@[grind .]
theorem Star.plus (R : α → α → Prop) :
    R^+ x z →
    R^* x z := by
  apply Star.unfold_l

theorem Star.unfold_r (R : α → α → Prop) :
    (R^* ∘ R) x z →
    R^* x z := by
  intro h
  rcases h with ⟨y, ⟨hl, hr⟩⟩
  induction hl
  case base =>
    right
    apply hr
    left
  case iter hll hlr ih =>
    right
    apply hll
    apply ih
    apply hr

@[grind .]
theorem Plus.once : R x y → R^+ x y := by
  intros h
  exists y <;> grind

theorem Plus.unfold_r : Plus R = Dot (Star R) R := by
  funext x y
  apply PartialOrder.rel_antisymm
  · simp only [PartialOrder.rel]
    intros h
    rcases h with ⟨x', hl, hr⟩
    revert x
    induction hr
    case base y' =>
      intros x hR
      exists x
      grind
    case iter a b c hl' hr ih =>
      intros x hR
      have ih := ih a hl'
      rw [Star.trans', Dot.assoc.assoc]
      exists a
      grind
  · simp only [PartialOrder.rel]
    intros h
    rcases h with ⟨x', hl, hr⟩
    revert y
    induction hl
    case base y' =>
      intros y hR
      exists y
      grind
    case iter a b c hl hr ih =>
      intros z hR
      exists b
      grind

end
