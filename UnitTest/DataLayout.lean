import Veir.DataLayout.RISCV64

open Veir

/-!
  Layout facts for the RV64 target. The interpreter and `isel-riscv64` both
  answer stride questions from this one layout, so these numbers pin down the
  addresses both of them compute.
-/

private def rv64 : DataLayout := .riscv64

private def i (bitwidth : Nat) : Attribute := .integerType { bitwidth }

private def arr (size : Nat) (type : Attribute) : Attribute := .llvmArrayType { size, type }

/- Whole-byte integers: size, ABI alignment and stride all agree. -/

#guard rv64.getTypeSize (i 8) == some 1
#guard rv64.getTypeAllocSize (i 8) == some 1
#guard rv64.getTypeABIAlignment (i 8) == some 1

#guard rv64.getTypeSize (i 32) == some 4
#guard rv64.getTypeAllocSize (i 32) == some 4
#guard rv64.getTypeABIAlignment (i 32) == some 4

#guard rv64.getTypeSize (i 64) == some 8
#guard rv64.getTypeAllocSize (i 64) == some 8
#guard rv64.getTypeABIAlignment (i 64) == some 8

/-
  Odd widths are where size and stride part ways: an `i24` occupies three bytes
  but consecutive `i24`s sit four bytes apart, because the width takes the ABI
  alignment of the next larger entry (`i32:32`).
-/

#guard rv64.getTypeSize (i 24) == some 3
#guard rv64.getTypeABIAlignment (i 24) == some 4
#guard rv64.getTypeAllocSize (i 24) == some 4

#guard rv64.getTypeSize (i 1) == some 1
#guard rv64.getTypeAllocSize (i 1) == some 1

/- A width above every entry takes the largest one, `i128:128`. -/

#guard rv64.getTypeABIAlignment (i 200) == some 16
#guard rv64.getTypeSize (i 200) == some 25
#guard rv64.getTypeAllocSize (i 200) == some 32

/- Zero-width integers have no layout. -/

#guard rv64.getTypeSize (i 0) == none

/- Arrays are laid out by their element's stride, so tail padding is included. -/

#guard rv64.getTypeSize (arr 3 (i 24)) == some 12
#guard rv64.getTypeAllocSize (arr 3 (i 24)) == some 12
#guard rv64.getTypeABIAlignment (arr 3 (i 24)) == some 4

#guard rv64.getTypeSize (arr 8 (i 8)) == some 8
#guard rv64.getTypeSize (arr 2 (arr 3 (i 24))) == some 24

/- Pointers are 64-bit, and floats take their natural alignment. -/

#guard rv64.getTypeSize (.llvmPointerType .mk) == some 8
#guard rv64.getTypeAllocSize (.llvmPointerType .mk) == some 8

#guard rv64.getTypeSize (.floatType .f32) == some 4
#guard rv64.getTypeABIAlignment (.floatType .f32) == some 4
#guard rv64.getTypeSize (.floatType .f64) == some 8
#guard rv64.getTypeABIAlignment (.floatType .f64) == some 8

/- A type with no layout entry, such as a function type, answers `none`. -/

#guard rv64.getTypeSize (.functionType { inputs := #[], outputs := #[] }) == none
