module

public import Veir.IR.Attribute

/-!
# DataLayoutInterface

Target data layouts answer physical representation queries for IR types.  The
interface deliberately distinguishes the byte size of a type, its ABI and
preferred alignments, and its allocation size (the stride between consecutive
objects). In particular, an odd-width integer can have a three-byte type size
but a four-byte allocation size.
-/

namespace Veir

public section

/-- Round `size` up to a positive byte alignment. -/
private def alignTo (size alignment : Nat) : Nat :=
  if alignment = 0 then size
  else ((size + alignment - 1) / alignment) * alignment

/-- The fixed-size layout facts for one type, all expressed in bytes. -/
structure DataLayoutTypeInfo where
  size : Nat
  abiAlignment : Nat
  preferredAlignment : Nat
deriving Inhabited, Repr, DecidableEq

/--
  The allocation size of the type, in bytes: the stride between consecutive
  objects, including tail padding required by the ABI alignment.
-/
def DataLayoutTypeInfo.allocSize (info : DataLayoutTypeInfo) : Nat :=
  alignTo info.size info.abiAlignment

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

end DataLayout

end

end Veir
