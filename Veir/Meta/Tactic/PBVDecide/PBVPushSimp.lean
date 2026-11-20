module

public import Lean

/-- Simp label for the push theorems. -/
register_simp_attr pbv_push
/-- Label for the theorems that lift from bv to `setWidth`. -/
register_label_attr pbv_lift
/-- Label for push theorems that need explicit bounds. -/
register_label_attr pbv_push_bound
