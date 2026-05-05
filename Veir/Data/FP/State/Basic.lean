module

namespace Veir.Data.FP

public section

/--
A plain enumeration of the possible states of a floating point value.
We define this separately to enable bitblasting the state of a FP value,
and to enable a shared representation of the FP state across
packed/unpacked representations.
-/
inductive State
/-- A zero floating point value. -/
| zero
/-- A finite subnormal value. -/
| subnormal
/-- A finite normal value. -/
| normal
/-- An infinite value. -/
| infinite
/-- A not a number (NaN) value. -/
| nan
deriving DecidableEq, Repr

namespace State

/-- A state is finite iff it is zero, subnormal, or normal. -/
@[expose]
def isFinite (s : State) : Prop :=
  s = .zero ∨ s = .subnormal ∨ s = .normal

instance {s : State} : Decidable (s.isFinite) := by
  simp [State.isFinite]
  infer_instance

/-- A state is nonzero finite iff it is subnormal or normal. -/
@[expose]
def isNonzeroFinite (s : State) : Prop :=
  s = .subnormal ∨ s = .normal

instance {s : State} : Decidable (s.isNonzeroFinite) := by
  simp [State.isNonzeroFinite]
  infer_instance

end State
end -- public section
end Veir.Data.FP

