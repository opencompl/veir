module

public import Veir.OpCode

public section

namespace Veir

/--
The opcodes proved monotone in CTrees, in their operands and their memory, loads included: those
of gMIR, LLVM, RISC-V, `gmir_riscv`, `riscv_stack`, `cf`, `riscv_cf`, `func`, `builtin` and
`test`, whose operations have no semantics and fail. The proofs are in
`Veir.Dialects.ProvedMonotone`; the set is here so that a pass can check it.
-/
@[expose]
def OpCode.treeMonotoneProved : OpCode → Bool
  | .gmir _ | .llvm _ | .riscv _ | .gmir_riscv _ | .riscv_stack _ | .cf _ | .riscv_cf _ | .func _
  | .builtin _ | .test _ => true
  | _ => false

end Veir

end
