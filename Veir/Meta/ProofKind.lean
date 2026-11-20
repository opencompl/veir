module

public import Lean

/-! ## How a rewrite's validity is proven

Every theorem that certifies a rewrite (a `Pattern.Valid` theorem, which a `Status` lemma or a
`Certificates` cell points at) carries exactly one of these labels, saying how it is proven. The
evaluation scripts count rewrites by them. A proof that does real work by hand counts as manual,
even if it calls a decision procedure for some goals along the way.
-/

/-- Proven by hand. -/
register_label_attr proof_manual
/-- Proven by `pbv_decide` (`veir_pbv_decide`), after the standard opening of a validity proof. -/
register_label_attr proof_pbv
/-- Proven by `bv_decide` (`veir_bv_decide`), after the standard opening of a validity proof. -/
register_label_attr proof_bv
/-- Proven by `veir_bv_normalize` alone, after the standard opening of a validity proof. -/
register_label_attr proof_norm
