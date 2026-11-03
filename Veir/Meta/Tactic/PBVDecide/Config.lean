module

public meta import Lean.Elab.Tactic
import Lean.Elab.ConfigEval

public section

namespace Veir.Meta.Tactic.PBVDecide

/--
User facing config for the tactic.
-/
structure PbvDecideConfig where
  /-- Whether or not `bv_decide` should be run on the final goals. -/
  bv_decide : Bool := true
  /-- Whether or not `grind` should be run on the generated side goals. -/
  grind : Bool := true

declare_config_elab elabPbvDecideConfig PbvDecideConfig

/--
Read-only configuration for the tactic.
-/
structure PbvDecideContext where
  /-- The bound up to which we want to bitblast our widths. -/
  bmcBound : Nat
  /-- The user provided config. -/
  config : PbvDecideConfig

end Veir.Meta.Tactic.PBVDecide
