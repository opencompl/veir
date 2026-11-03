module

public import Veir.Dialects.LLVM.Monotonicity
public import Veir.Dialects.RISCV.Monotonicity

public section

/-!
# Monotonicity of the dialects

Every opcode is monotone in its operands: the opcodes that have a proof through their own
instance, the rest by assumption. The split is per opcode, so a dialect can prove the ones it
can and leave the rest. Importing this module is what gives `interpretOp'_monotone` an opcode
it knows nothing about.
-/

namespace Veir

instance (priority := low) (opType : OpCode) : InterpretOp'Monotone opType := by
  cases opType <;> rename_i op <;> cases op <;>
    first
      | infer_instance
      | exact interpretOp'_monotone_assumed _

end Veir

end
