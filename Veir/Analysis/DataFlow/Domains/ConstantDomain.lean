module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.FoldDecision
public import Veir.Interpreter.Refinement.Basic
import Veir.Interpreter.Refinement.Lemmas

public section

namespace Veir

/-!
# Constant domain

Instantiation of `AbstractDomain` with a constant propagation lattice whose
elements are `bottom`, a constant, or `top`.
-/

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

/--
The order of the constant domain: `⊥` is below everything, everything is below `⊤`,
and `constant c ≤ constant d` when `c` is refined by `d`.
-/
def le (x y : AbstractConstant) : Prop :=
  match x, y with
  | .bottom, _ => True
  | _, .top => True
  | .constant c, .constant d => c ⊒ d
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

/--
Least upper bound. Two constants join to the least value both refine to, or to `⊤` if there
is none. Since `≤` on constants is `⊒`, this is the greatest lower bound under refinement
(`RuntimeValue.glb?`).
-/
def join (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .bottom, y => y
  | x, .bottom => x
  | .top, _ => ⊤
  | _, .top => ⊤
  | .constant c, .constant d =>
    match c.glb? d with
    | some e => .constant e
    | none => ⊤

instance : Join AbstractConstant where
  join := join

theorem γ_monotone (a b : AbstractConstant) : a ≤ b → γ a ⊆ γ b := by
  intro hab x hx
  cases a <;> cases b <;> simp only [LE.le, le] at hab
  all_goals first | trivial | exact hab.elim | exact hx.elim | skip
  case constant.constant c d => exact RuntimeValue.isRefinedBy_trans hx hab

@[simp, grind .]
theorem le_refl (a : AbstractConstant) : a ≤ a := by
  cases a <;> first | trivial | exact RuntimeValue.isRefinedBy_refl _

@[grind →]
theorem le_trans (a b c : AbstractConstant) : a ≤ b → b ≤ c → a ≤ c := by
  intro h h'
  cases a <;> cases b <;> cases c <;> simp only [le_def, le] at h h' ⊢ <;>
    first | trivial | exact h.elim | exact h'.elim | exact RuntimeValue.isRefinedBy_trans h h'

@[grind →]
theorem le_antisymm (a b : AbstractConstant) : a ≤ b → b ≤ a → a = b := by
  intro h h'
  cases a <;> cases b <;> simp only [le_def, le] at h h' ⊢ <;>
    first | rfl | exact h.elim | exact h'.elim | rw [RuntimeValue.isRefinedBy_antisymm h h']

@[simp, grind .]
theorem le_join_left (a b : AbstractConstant) : a ≤ a ⊔ b := by
  show a ≤ join a b
  cases a <;> cases b <;> simp only [join] <;>
    first | exact le_refl _ | exact le_top _ | exact bot_le _ | skip
  case constant.constant c d =>
    split
    · next e he => exact (RuntimeValue.glb?_isRefinedBy he).1
    · exact le_top _

@[simp, grind .]
theorem le_join_right (a b : AbstractConstant) : b ≤ a ⊔ b := by
  show b ≤ join a b
  cases a <;> cases b <;> simp only [join] <;>
    first | exact le_refl _ | exact le_top _ | exact bot_le _ | skip
  case constant.constant c d =>
    split
    · next e he => exact (RuntimeValue.glb?_isRefinedBy he).2
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
      obtain ⟨m, hm, hme⟩ := RuntimeValue.glb?_greatest ha hb
      simp only [hm]
      exact hme

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
