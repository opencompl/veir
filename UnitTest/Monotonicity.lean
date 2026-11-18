import Veir.Dialects.Monotonicity

/-!
Test which axioms the monotonicity of the dialects depends on: an opcode proved monotone in
CTrees depends on the `Sim` axioms only, and the rest on `OpCode.interpretCTree_monotone_assumed`.
-/

namespace Veir

/-- Instance resolution proves, rather than assumes, every `cf` opcode monotone in CTrees. -/
theorem cf_interpretOpMonotone_not_assumed (op : Cf) : InterpretOpMonotone (.cf op) :=
  inferInstance

/--
info: 'Veir.cf_interpretOpMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms cf_interpretOpMonotone_not_assumed

/--
info: 'Veir.OpCode.interpretCTree_monotone_of_opCode' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub,
 OpCode.interpretCTree_monotone_assumed]
-/
#guard_msgs in
#print axioms OpCode.interpretCTree_monotone_of_opCode

end Veir
