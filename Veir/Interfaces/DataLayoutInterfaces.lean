module

public import Veir.IR.Attribute

/-!
# DataLayoutInterface

Target data layouts answer physical representation queries for IR types.  The
interface deliberately distinguishes the byte size of a type, its ABI and
preferred alignments, and its allocation size (the stride between consecutive
objects).  In particular, an odd-width integer can have a three-byte type size
but a four-byte allocation size.

The current implementation is the fixed layout used by the RV64 instruction
selector.  A future implementation can construct the same interface from a
module's `dlti.dl_spec` without changing clients.
-/

namespace Veir

public section

/-- The fixed-size layout facts for one type, all expressed in bytes. -/
structure DataLayoutTypeInfo where
  size : Nat
  abiAlignment : Nat
  preferredAlignment : Nat
  allocSize : Nat
deriving Inhabited, Repr, DecidableEq

/--
  A target data layout. Unsupported or unsized types return `none`.

  Keeping the query behind an object lets passes depend on the interface rather
  than on how layout information is obtained (currently fixed RV64 values,
  eventually perhaps parsed DLTI entries).
-/
structure DataLayout where
  query : Attribute → Option DataLayoutTypeInfo

namespace DataLayout

/-- Return the size of `type` in bytes, including padding internal to the type. -/
def getTypeSize (layout : DataLayout) (type : Attribute) : Option Nat :=
  (layout.query type).map (·.size)

/-- Return the minimum ABI-required alignment of `type`, in bytes. -/
def getTypeABIAlignment (layout : DataLayout) (type : Attribute) : Option Nat :=
  (layout.query type).map (·.abiAlignment)

/-- Return the preferred alignment of `type`, in bytes. -/
def getTypePreferredAlignment (layout : DataLayout) (type : Attribute) : Option Nat :=
  (layout.query type).map (·.preferredAlignment)

/--
  Return the allocation size of `type`, in bytes: the stride between consecutive
  objects, including tail padding required by the ABI alignment.
-/
def getTypeAllocSize (layout : DataLayout) (type : Attribute) : Option Nat :=
  (layout.query type).map (·.allocSize)

/-- Round `size` up to a positive byte alignment. -/
private def alignTo (size alignment : Nat) : Nat :=
  if alignment = 0 then size
  else ((size + alignment - 1) / alignment) * alignment

/-- The smallest power of two greater than or equal to `n` (and `1` for `0`). -/
private def powerOfTwoCeil (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)

/--
  RV64 integer ABI alignment, derived from LLVM's
  `i1:8-i8:8-i16:16-i32:32-i64:64-i128:128` layout entries. As in LLVM and
  MLIR, an unlisted width uses the next larger entry, or the largest entry when
  no larger one exists.
-/
private def rv64IntegerAlignment (bitwidth : Nat) : Nat :=
  if bitwidth ≤ 8 then 1
  else if bitwidth ≤ 16 then 2
  else if bitwidth ≤ 32 then 4
  else if bitwidth ≤ 64 then 8
  else 16

private def scalarInfo (size alignment : Nat) : DataLayoutTypeInfo :=
  { size
    abiAlignment := alignment
    preferredAlignment := alignment
    allocSize := alignTo size alignment }

/-- Layout facts for the LLVM-compatible fixed-size types supported by VeIR. -/
private def queryRISCV64 (type : Attribute) : Option DataLayoutTypeInfo :=
  match type with
  | .integerType { bitwidth } | .byteType { bitwidth } =>
      if bitwidth = 0 then none
      else
        let size := (bitwidth + 7) / 8
        some (scalarInfo size (rv64IntegerAlignment bitwidth))
  | .floatType { bitwidth } =>
      if bitwidth = 0 then none
      else
        let size := (bitwidth + 7) / 8
        some (scalarInfo size (powerOfTwoCeil size))
  | .llvmPointerType _ =>
      some (scalarInfo 8 8)
  | .llvmArrayType { size, type } => do
      let element ← queryRISCV64 type
      let arraySize := element.allocSize * size
      some
        { size := arraySize
          abiAlignment := element.abiAlignment
          preferredAlignment := element.preferredAlignment
          allocSize := alignTo arraySize element.abiAlignment }
  | _ => none

/--
  The standard RV64 data layout:
  `e-m:e-p:64:64-i64:64-i128:128-n32:64-S128`, together with LLVM's
  default primitive entries.
-/
def riscv64 : DataLayout :=
  { query := queryRISCV64 }

end DataLayout

end

end Veir
