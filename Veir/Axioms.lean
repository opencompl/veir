import Veir.Rewriter.WellFormed.Value
import Veir.Rewriter.WellFormed.OpOperands
import Veir.Rewriter.WellFormed.BlockOperands

open Veir

/--
info: 'Veir.Rewriter.replaceValue?_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.replaceValue?_WellFormed

/--
info: 'Veir.Rewriter.pushOperand_DefUse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.pushOperand_DefUse

/--
info: 'Veir.Rewriter.pushOperand_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.pushOperand_WellFormed

/--
info: 'Veir.Rewriter.pushBlockOperand_DefUse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.pushBlockOperand_DefUse

/--
info: 'Veir.Rewriter.pushBlockOperand_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.pushBlockOperand_WellFormed
