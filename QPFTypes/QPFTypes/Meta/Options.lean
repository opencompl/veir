module

public import Lean

/-! # QPFTypes Options & Trace Class -/

initialize Lean.registerTraceClass `QPFTypes

public register_option QPFTypes.debug : Bool := {
  defValue := false
  descr := "Enable debug assertions in the QPFTypes library"
}
