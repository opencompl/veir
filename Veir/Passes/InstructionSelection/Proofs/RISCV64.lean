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

The 155 original placeholders have 121 proofs and 34 concrete semantic
counterexamples. Counterexample witnesses are proved in the corresponding
submodules; the false validity declarations retain annotated `sorry` bodies.
Those declarations are not established validity results.

| File | Proved | Counterexamples |
| --- | ---: | ---: |
| Arithmetic | 19 | 0 |
| BitManipulation | 21 | 0 |
| Bitwise | 12 | 0 |
| Casts | 16 | 3 |
| Comparisons | 21 | 0 |
| Constants | 5 | 1 |
| Loads | 0 | 15 |
| Memory | 0 | 3 |
| Rotates | 14 | 0 |
| Shifts | 13 | 0 |
| Stores | 0 | 12 |

Matched operations now carry `IsFromVerifiedOp` premises. These discharge twenty
obligations previously blocked by operand/result type mismatches or inconsistent
constant-attribute types. Earlier unverified semantic witnesses retained in the
submodules do not refute these verified-source validity statements.

The remaining counterexamples involve values wider than a register,
pointer-object identity loss without runtime memory invariants, and
unimplemented intrinsic-call semantics. IR verification alone does not exclude
those cases.
-/
