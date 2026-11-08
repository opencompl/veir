module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Arithmetic
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.BitManipulation
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Bitwise
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Casts
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Comparisons
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Constants
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Loads
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Memory
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Rotates
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Shifts
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Stores

/-! CTree validity proofs for the RISC-V 64-bit instruction-selection patterns.

Proofs are grouped by operation family in the `RISCV64` submodules. Parameterized
builders are covered at the instantiations used by the instruction selector,
including every element of its generated pattern arrays. -/

/-! ## Placeholder audit

The 155 original placeholders have 101 proofs and 54 concrete semantic
counterexamples. Counterexample witnesses are proved in the corresponding
submodules; the false validity declarations retain annotated `sorry` bodies.
Those declarations are not established validity results.

| File | Proved | Counterexamples |
| --- | ---: | ---: |
| Arithmetic | 19 | 0 |
| BitManipulation | 19 | 2 |
| Bitwise | 12 | 0 |
| Casts | 12 | 7 |
| Comparisons | 17 | 4 |
| Constants | 5 | 1 |
| Loads | 0 | 15 |
| Memory | 0 | 3 |
| Rotates | 4 | 10 |
| Shifts | 13 | 0 |
| Stores | 0 | 12 |

The counterexamples expose missing operand/result typing constraints, values
wider than a register, inconsistent constant-attribute widths, pointer-object
identity loss without memory invariants, and unimplemented intrinsic-call
semantics. They concern the current unrestricted pattern-validity statements;
some witnesses use inputs that a separate IR verifier would reject.
-/
