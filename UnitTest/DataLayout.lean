import Veir.DataLayout.RISCV64

/-! Tests for fixed RV64 data-layout queries. -/

open Veir

private def rv64 := DataLayout.riscv64

#guard rv64.getTypeSize (IntegerType.mk 24) = some 3
#guard rv64.getTypeABIAlignment (IntegerType.mk 24) = some 4
#guard rv64.getTypePreferredAlignment (IntegerType.mk 24) = some 4
#guard rv64.getTypeAllocSize (IntegerType.mk 24) = some 4

#guard rv64.getTypeSize (IntegerType.mk 42) = some 6
#guard rv64.getTypeABIAlignment (IntegerType.mk 42) = some 8
#guard rv64.getTypeAllocSize (IntegerType.mk 42) = some 8

#guard rv64.getTypeSize (IntegerType.mk 65) = some 9
#guard rv64.getTypeABIAlignment (IntegerType.mk 65) = some 16
#guard rv64.getTypeAllocSize (IntegerType.mk 65) = some 16

#guard rv64.getTypeSize (IntegerType.mk 129) = some 17
#guard rv64.getTypeABIAlignment (IntegerType.mk 129) = some 16
#guard rv64.getTypeAllocSize (IntegerType.mk 129) = some 32

#guard rv64.getTypeSize LLVM.PointerType.mk = some 8
#guard rv64.getTypeABIAlignment LLVM.PointerType.mk = some 8

private def twoI24 : Attribute := LLVM.ArrayType.mk 2 (IntegerType.mk 24)

#guard rv64.getTypeSize twoI24 = some 8
#guard rv64.getTypeABIAlignment twoI24 = some 4
#guard rv64.getTypeAllocSize twoI24 = some 8

private def nestedOddWidthArray : Attribute :=
  LLVM.ArrayType.mk 3 (LLVM.ArrayType.mk 2 (IntegerType.mk 24))

#guard rv64.getTypeSize nestedOddWidthArray = some 24
#guard rv64.getTypeABIAlignment nestedOddWidthArray = some 4
#guard rv64.getTypeAllocSize nestedOddWidthArray = some 24

#guard rv64.getTypeSize (LLVM.VoidType.mk : Attribute) = none
