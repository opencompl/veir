import Veir.Dialects.ResultsConform

/-! Test that a given dialect's conformance depends only on Lean's standard axioms. -/

namespace Veir

theorem cf_resultsConform_not_assumed (op : Cf) : ResultsConform (.cf op) :=
  inferInstance

/--
info: 'Veir.cf_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cf_resultsConform_not_assumed

end Veir
