module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Arithmetic
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.BitManipulation
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Bitwise
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Casts
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Comparisons
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Constants
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.GMIRLoads
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.GMIRFoldedLoads
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Loads
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Memory
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Rotates
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Shifts
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Selects
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.StorePatterns
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Coverage

/-! CTree validity proofs for the RISC-V 64-bit instruction-selection patterns.

Proofs are grouped by operation family in the `RISCV64` submodules. Parameterized
builders are covered at the instantiations used by the instruction selector,
including every element of its generated pattern arrays. -/

/-! ## Proof coverage

There are 163 proved concrete Puddle pattern instances and four excluded instances
with checked semantic counterexamples. `RISCV64Proofs.provedPatterns` packages
each proved pattern with its validity theorem, and `provedPatterns_size` checks
the total. Native procedural rewrites are outside this Puddle inventory.

| Family | Proved |
| --- | ---: |
| Arithmetic | 19 |
| BitManipulation | 21 |
| Bitwise | 12 |
| Casts | 11 |
| Comparisons | 21 |
| Constants | 5 |
| LLVM loads | 12 |
| GMIR loads | 12 |
| Address and lifetime | 3 |
| Rotates | 14 |
| Fused comparison/select | 8 |
| Shifts | 13 |
| Stores | 12 |

Matched operation metadata carries `IsFromVerifiedOp` premises. The proofs use
the address-only pointer model and memory refinement, including resolution of
poison bits by register conversions and stores.

The two wide GMIR casts still lose defined bits above bit 63. The memcpy/memset
call fallbacks still lack local call semantics. Their checked witnesses are in
`Casts` and `Memory`; no validity theorem is exported for these four patterns.
There are no admitted validity declarations in this suite.
-/
