module

public import Lean

/-- Simp label for the push theorems. -/
register_simp_attr pbv_push
/--
Simp label for the theorems unfolding operations defined in terms of other `BitVec`
operations (`extractLsb`, `rotateLeft`, ...). They are applied before reification, so that
the widths and `Nat` values they expose are reified.
-/
register_simp_attr pbv_unfold
/-- Label for the theorems that lift from bv to `setWidth`. -/
register_label_attr pbv_lift
/-- Label for push theorems that need explicit bounds. -/
register_label_attr pbv_push_bound
