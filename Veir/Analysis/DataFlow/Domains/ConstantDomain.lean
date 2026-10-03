module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.FoldDecision
public import Veir.Interpreter.Refinement.Basic
import Veir.Interpreter.Refinement.Lemmas
import all Veir.Data.Refinement
import all Veir.Data.LLVM.Byte.Basic

public section

namespace Veir

/-!
# Constant domain

Instantiation of `AbstractDomain` with a constant propagation lattice whose
elements are `bottom`, a constant, or `top`.
-/

namespace RuntimeValue

/-- The poison of `v`'s kind and width, or `v` itself for kinds without poison. -/
def poisonOf : RuntimeValue → RuntimeValue
  | .int w _ => .int w .poison
  | .byte w _ => .byte w Data.LLVM.Byte.allPoison
  | .addr _ => .addr .poison
  | v => v

@[simp] theorem poisonOf_poisonOf (v : RuntimeValue) : v.poisonOf.poisonOf = v.poisonOf := by
  cases v <;> rfl

/-- The poison of a value's kind is refined by the value. -/
theorem poisonOf_isRefinedBy (v : RuntimeValue) : v.poisonOf ⊒ v := by
  cases v with
  | int w t => exact ⟨rfl, by simp [Data.LLVM.Int.cast_self, _root_.isRefinedBy]⟩
  | byte w b => exact ⟨rfl, by simp [Data.LLVM.Byte.isRefinedBy, Data.LLVM.Byte.allPoison]⟩
  | addr p => show Data.LLVM.Ptr.poison ⊒ p; trivial
  | _ => exact RuntimeValue.isRefinedBy_refl _

end RuntimeValue

/-- Abstract values used by sparse constant propagation. -/
inductive AbstractConstant where
  | top
  | bottom
  | constant (value : RuntimeValue)
deriving BEq, DecidableEq, TypeName

instance : ToString AbstractConstant where
  toString
    | .top => "top"
    | .bottom => "bottom"
    | .constant value => s!"const({value})"

namespace AbstractConstant

/-- `c ≼ d`: `c` is `d`, or the poison of `d`'s kind. -/
notation:50 c:51 " ≼ " d:51 => c = d ∨ c = RuntimeValue.poisonOf d

theorem below_refl (c : RuntimeValue) : c ≼ c := Or.inl rfl

theorem below_trans {c d e : RuntimeValue} (hcd : c ≼ d) (hde : d ≼ e) : c ≼ e := by
  rcases hde with rfl | rfl
  · exact hcd
  · rcases hcd with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inr (RuntimeValue.poisonOf_poisonOf e)

theorem below_antisymm {c d : RuntimeValue} (hcd : c ≼ d) (hdc : d ≼ c) : c = d := by
  rcases hcd with rfl | rfl
  · rfl
  · rcases hdc with h | h
    · exact h.symm
    · rw [RuntimeValue.poisonOf_poisonOf] at h; exact h.symm

/-- Two constants below a common one are comparable. -/
theorem below_total_of_below {c d e : RuntimeValue} (hce : c ≼ e) (hde : d ≼ e) :
    c ≼ d ∨ d ≼ c := by
  rcases hce with rfl | rfl <;> rcases hde with rfl | rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inl (Or.inl rfl)

/-- Defines the ordering of abstract values in the constant domain. -/
def le (x y : AbstractConstant) : Prop :=
  match x, y with
  | .bottom, _ => True
  | _, .top => True
  | .constant c, .constant d => c ≼ d
  | _, _ => False

instance : LE AbstractConstant where
  le := le

theorem le_def (a b : AbstractConstant) : (a ≤ b) ↔ le a b := Iff.rfl

@[simp, grind .]
theorem le_top (a : AbstractConstant) : a ≤ .top := by
  cases a <;> trivial

@[simp, grind .]
theorem bot_le (a : AbstractConstant) : .bottom ≤ a := by
  cases a <;> trivial

instance : BoundedOrder AbstractConstant where
  top := .top
  bot := .bottom
  le_top := le_top
  bot_le := bot_le

def ofFoldDecision (result : FoldDecision) (operands : Array AbstractConstant) : AbstractConstant :=
  match result with
  | .useOperand index => operands[index]?.getD ⊤
  | .useConstant value => .constant value

@[expose] def γ (absVal : AbstractConstant) : Set RuntimeValue :=
  match absVal with
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .constant a => fun source => RuntimeValue.isRefinedBy source a

def join (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .bottom, y => y
  | x, .bottom => x
  | .top, _ => ⊤
  | _, .top => ⊤
  | .constant c, .constant d =>
    if c ≼ d then .constant d else if d ≼ c then .constant c else ⊤

instance : Join AbstractConstant where
  join := join

theorem γ_monotone (a b : AbstractConstant) : a ≤ b → γ a ⊆ γ b := by
  intro hab x hx
  cases a <;> cases b <;> simp only [LE.le, le] at hab
  all_goals first | trivial | exact hab.elim | exact hx.elim | skip
  case constant.constant c d =>
    rcases hab with rfl | rfl
    · exact hx
    · exact RuntimeValue.isRefinedBy_trans hx (RuntimeValue.poisonOf_isRefinedBy d)

@[simp, grind .]
theorem le_refl (a : AbstractConstant) : a ≤ a := by
  cases a <;> simp [le, le_def]

@[grind →]
theorem le_trans (a b c : AbstractConstant) : a ≤ b → b ≤ c → a ≤ c := by
  intro h h'
  cases a <;> cases b <;> cases c <;> simp only [le_def, le] at h h' ⊢ <;>
    first | trivial | exact h.elim | exact h'.elim | exact below_trans h h'

@[grind →]
theorem le_antisymm (a b : AbstractConstant) : a ≤ b → b ≤ a → a = b := by
  intro h h'
  cases a <;> cases b <;> simp only [le_def, le] at h h' ⊢ <;>
    first | rfl | exact h.elim | exact h'.elim | rw [below_antisymm h h']

@[simp, grind .]
theorem le_join_left (a b : AbstractConstant) : a ≤ a ⊔ b := by
  show a ≤ join a b
  cases a <;> cases b <;> simp only [join] <;>
    first | exact le_refl _ | exact le_top _ | exact bot_le _ | skip
  case constant.constant c d =>
    split
    · next h => exact h
    · split
      · exact below_refl c
      · exact le_top _

@[simp, grind .]
theorem le_join_right (a b : AbstractConstant) : b ≤ a ⊔ b := by
  show b ≤ join a b
  cases a <;> cases b <;> simp only [join] <;>
    first | exact le_refl _ | exact le_top _ | exact bot_le _ | skip
  case constant.constant c d =>
    split
    · exact below_refl d
    · split
      · next h => exact h
      · exact le_top _

theorem join_le (a b c : AbstractConstant) : a ≤ c → b ≤ c → a ⊔ b ≤ c := by
  intro ha hb
  show join a b ≤ c
  cases a <;> cases b <;> simp only [join] <;> first | exact ha | exact hb | exact bot_le _ | skip
  case constant.constant c' d' =>
    cases c with
    | top => exact le_top _
    | bottom => exact ha.elim
    | constant e =>
      simp only [le_def, le] at ha hb
      split
      · exact hb
      · split
        · exact ha
        · rcases below_total_of_below ha hb with h | h <;> contradiction

instance : JoinSemilattice AbstractConstant where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  join := join
  le_join_left := le_join_left
  le_join_right := le_join_right
  join_le := join_le

instance : AbstractDomain AbstractConstant RuntimeValue where
  toJoinSemilattice := inferInstance
  toBoundedOrder := inferInstance
  γ := γ
  γ_top := rfl
  γ_bot := rfl
  γ_monotone := γ_monotone

end AbstractConstant

end Veir
