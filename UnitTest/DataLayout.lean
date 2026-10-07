import Veir.DataLayout.RISCV64

open Veir

private def intType (bitwidth : Nat) : Attribute :=
  .integerType { bitwidth }

private def intVector (count bitwidth : Nat) : Attribute :=
  .vectorType { shape := #[count], elementType := intType bitwidth }

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

private def llvmStruct (body : Array Attribute) (packed : Bool := false) : Attribute :=
  .llvmStructType { name := none, packed, body }

private def fieldOffset (type : Attribute) (field : Int) : Option Int :=
  (DataLayout.riscv64.gepOffsets (α := Unit) type #[.const 0, .const field]).map (·.1)

-- Field alignment and tail padding both contribute to struct layout.
private def padded := llvmStruct #[intType 32, intType 64]
#guard DataLayout.riscv64.query padded =
  some { size := 16, abiAlignment := 8, preferredAlignment := 8 }
#guard fieldOffset padded 1 = some 8
private def tailPadded := llvmStruct #[intType 64, intType 8]
#guard DataLayout.riscv64.getTypeAllocSize tailPadded = some 16
#guard fieldOffset tailPadded 1 = some 8

-- Packed structs have byte alignment; nested structs preserve their own layout.
private def packed := llvmStruct #[intType 8, intType 32] true
#guard DataLayout.riscv64.query packed =
  some { size := 5, abiAlignment := 1, preferredAlignment := 8 }
#guard fieldOffset packed 1 = some 1
private def nested := llvmStruct #[intType 8, packed, intType 16]
#guard DataLayout.riscv64.query nested =
  some { size := 8, abiAlignment := 2, preferredAlignment := 8 }
#guard fieldOffset nested 1 = some 1
#guard fieldOffset nested 2 = some 6

-- Arrays use the allocation stride of their elements, including i24 padding.
private def arrayField := llvmStruct
  #[intType 8, .llvmArrayType { size := 3, type := intType 24 }]
#guard DataLayout.riscv64.query arrayField =
  some { size := 16, abiAlignment := 4, preferredAlignment := 8 }
#guard fieldOffset arrayField 1 = some 4

-- Identified structs with bodies and empty structs have ordinary layouts too.
private def namedGrid : Attribute :=
  let row := Attribute.llvmArrayType { size := 9, type := intType 8 }
  .llvmStructType
    { name := some "grid".toUTF8, packed := false,
      body := #[.llvmArrayType { size := 9, type := row }] }
#guard DataLayout.riscv64.query namedGrid =
  some { size := 81, abiAlignment := 1, preferredAlignment := 8 }
#guard fieldOffset namedGrid 0 = some 0
#guard DataLayout.riscv64.query (llvmStruct #[]) =
  some { size := 0, abiAlignment := 1, preferredAlignment := 8 }
