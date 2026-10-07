import Veir.DataLayout.RISCV64

open Veir

private def intVector (count bitwidth : Nat) : Attribute :=
  .vectorType { shape := #[count], elementType := .integerType { bitwidth } }

-- Vector elements occupy their bit widths, without scalar allocation padding.
#guard DataLayout.riscv64.query (intVector 8 1) =
  some { size := 1, abiAlignment := 1, preferredAlignment := 1 }
#guard DataLayout.riscv64.query (intVector 9 1) =
  some { size := 2, abiAlignment := 2, preferredAlignment := 2 }
#guard DataLayout.riscv64.query (intVector 17 1) =
  some { size := 3, abiAlignment := 4, preferredAlignment := 4 }
#guard DataLayout.riscv64.getTypeAllocSize (intVector 17 1) = some 4
#guard DataLayout.riscv64.query (intVector 3 24) =
  some { size := 9, abiAlignment := 16, preferredAlignment := 16 }
#guard DataLayout.riscv64.query (intVector 5 24) =
  some { size := 15, abiAlignment := 16, preferredAlignment := 16 }
#guard DataLayout.riscv64.getTypeAllocSize (intVector 5 24) = some 16

-- Ordinary integer, floating-point and pointer vectors retain their layouts.
#guard DataLayout.riscv64.query (intVector 3 32) =
  some { size := 12, abiAlignment := 16, preferredAlignment := 16 }
#guard DataLayout.riscv64.query (.vectorType
    { shape := #[3], elementType := .floatType .f32 }) =
  some { size := 12, abiAlignment := 16, preferredAlignment := 16 }
#guard DataLayout.riscv64.query (.vectorType
    { shape := #[2], elementType := .llvmPointerType {} }) =
  some { size := 16, abiAlignment := 16, preferredAlignment := 16 }
#guard DataLayout.riscv64.query (intVector 4 0) = none
