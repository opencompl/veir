module

public import Veir.Dialects.RISCV.Monotonicity

public section

/-!
# Monotonicity of the dialects

Every opcode is monotone in its operands: the dialects that have a proof through their own
instance, the rest by assumption. Importing this module is what gives `interpretOp'_monotone`
an opcode it knows nothing about.
-/

namespace Veir

instance (priority := low) (opType : OpCode) : InterpretOp'Monotone opType := by
  cases opType
  case riscv op => infer_instance
  all_goals exact interpretOp'_monotone_assumed _

end Veir

end
