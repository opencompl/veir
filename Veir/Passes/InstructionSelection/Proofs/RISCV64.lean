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
