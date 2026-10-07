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
def alignTo (size alignment : Nat) : Nat :=
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
  LLVM's `StructLayout` for a struct whose fields have the layouts `fields`: each
  field is placed at the next multiple of its ABI alignment (1 if packed), and the
  size is rounded up to the largest field alignment. The default `a:8:64` entry
  makes the struct ABI alignment at least 1 and its preferred alignment at least
  8. Returns the byte offset of each field, and the layout of the struct.
-/
def structLayout (fields : Array DataLayoutTypeInfo) (packed : Bool) :
    Array Nat × DataLayoutTypeInfo := Id.run do
  let mut offsets := #[]
  let mut offset := 0
  let mut alignment := 1
  for info in fields do
    let fieldAlignment := if packed then 1 else info.abiAlignment
    offset := alignTo offset fieldAlignment
    offsets := offsets.push offset
    offset := offset + info.allocSize
    alignment := max alignment fieldAlignment
  return (offsets,
    { size := alignTo offset alignment
      abiAlignment := alignment
      preferredAlignment := max 8 alignment })

/-- One index of a `getelementptr`: a constant, or a dynamic value of type `α`. -/
inductive GEPIndex (α : Type) where
  | const (value : Int)
  | dynamic (value : α)

/--
  The indices of a `llvm.getelementptr`, in order: `rawConstantIndices` holds
  each constant index, and the sentinel `-2^31` for each dynamic one, which takes
  the next of the `dynamic` operands.
-/
def GEPIndex.decode [Inhabited α] (rawConstantIndices : Array Int) (dynamic : Array α) :
    Array (GEPIndex α) := Id.run do
  let mut next := 0
  let mut indices := #[]
  for raw in rawConstantIndices do
    if raw = -2147483648 then
      indices := indices.push (.dynamic dynamic[next]!)
      next := next + 1
    else
      indices := indices.push (.const raw)
  return indices

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

/--
  Decompose the address a `getelementptr` over `elemType` computes into a
  constant byte offset plus, for each dynamic index, its byte stride: the address
  is the base, plus the constant, plus each dynamic index times its stride. The
  first index steps over whole `elemType` objects; each later one steps into the
  current type, to an array element or to a struct field (whose index must be a
  constant). Any other type returns `none`.
-/
def gepOffsets (layout : DataLayout) (elemType : Attribute) (indices : Array (GEPIndex α)) :
    Option (Int × Array (α × Nat)) := do
  let mut offset : Int := 0
  let mut dynamic := #[]
  /- The type the next index steps through: the first index steps through an
     array of `elemType`. -/
  let mut outer := Attribute.llvmArrayType { size := 0, type := elemType }
  for index in indices do
    match outer, index with
    | .llvmArrayType { type, .. }, index =>
      let stride ← layout.getTypeAllocSize type
      match index with
      | .const c => offset := offset + c * stride
      | .dynamic v => dynamic := dynamic.push (v, stride)
      outer := type
    | .llvmStructType { packed, body, .. }, .const c =>
      let (offsets, _) := structLayout (← body.mapM layout.query) packed
      offset := offset + offsets[c.toNat]!
      outer := body[c.toNat]!
    | _, _ => none
  return (offset, dynamic)

end DataLayout

end

end Veir
