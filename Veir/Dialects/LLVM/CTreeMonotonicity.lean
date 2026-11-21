module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.LLVM.Monotonicity

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.LLVM.Interpreter

public section

/-!
# Monotonicity of the LLVM opcodes in CTrees

`llvm.load` runs its `Interp` semantics in CTrees, which is monotone in its operands and its
memory. The types of the results come from `ResultsConform`.
-/

namespace Veir

/-- `llvm.load` runs its `Interp` semantics in CTrees. -/
theorem CTree.interpretOp'_llvm_load (properties : propertiesOf (OpCode.llvm .load))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (regions : Array RegionPtr) :
    CTree.interpretOp' (.llvm .load) properties resultTypes operands blockOperands mem regions =
      monadLift
        (Veir.interpretOp' (.llvm .load) properties resultTypes operands blockOperands mem) := by
  rfl

instance [ResultsConform (.llvm .load)] : InterpretCTreeMonotone (.llvm .load) :=
  ⟨.of_lift CTree.interpretOp'_llvm_load⟩

end Veir

end
