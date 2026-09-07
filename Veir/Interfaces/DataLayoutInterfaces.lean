module

public import Veir.IR.Attribute

/-!
# DataLayoutInterface

Target data layouts answer physical representation queries for IR types.  The
interface deliberately distinguishes the byte size of a type, its ABI and
preferred alignments, and its allocation size (the stride between consecutive
objects). In particular, an odd-width integer can have a three-byte type size
but a four-byte allocation size.

A `DataLayout` is an opaque query object so that passes and the interpreter
depend on the interface rather than on where layout facts come from.  The
layouts VeIR ships are built from a `DataLayoutSpec`, a table of entries in the
style of an LLVM datalayout string; a parser for `#dlti.dl_spec` would produce
the same table.
-/

namespace Veir

public section

/-- Round `size` up to a positive byte alignment. -/
private def alignTo (size alignment : Nat) : Nat :=
  if alignment = 0 then size
  else ((size + alignment - 1) / alignment) * alignment

/-- The smallest power of two greater than or equal to `n` (and `1` for `0`). -/
private def powerOfTwoCeil (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)

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
  The entries of a target data layout, in the style of an LLVM datalayout
  string. This is the data a layout is built from; `DataLayout.ofSpec` turns it
  into the query object that passes and the interpreter consume.
-/
structure DataLayoutSpec where
  /--
    Integer ABI alignments as `(bitwidth, alignment in bytes)` pairs, ordered by
    increasing bitwidth, mirroring the `iN:A` entries of a datalayout string.
  -/
  integerAlignments : Array (Nat × Nat)
  /-- The size of a pointer, in bytes. -/
  pointerSize : Nat
  /-- The ABI alignment of a pointer, in bytes. -/
  pointerAlignment : Nat
deriving Inhabited, Repr, DecidableEq

namespace DataLayoutSpec

/--
  The ABI alignment of an integer of the given width. As in LLVM and MLIR, a
  width with no entry of its own uses the entry for the next larger width, or
  the largest entry when no larger one exists.
-/
def integerAlignment (spec : DataLayoutSpec) (bitwidth : Nat) : Nat :=
  match spec.integerAlignments.find? (bitwidth ≤ ·.1) with
  | some entry => entry.2
  | none => spec.integerAlignments.back!.2

private def scalarInfo (size alignment : Nat) : DataLayoutTypeInfo :=
  { size
    abiAlignment := alignment
    preferredAlignment := alignment }

/--
  Layout facts for the fixed-size types VeIR models. Aggregates take the
  allocation size of their element, so their own size includes the padding
  between consecutive elements.
-/
def query (spec : DataLayoutSpec) (type : Attribute) : Option DataLayoutTypeInfo :=
  match type with
  | .integerType { bitwidth } | .byteType { bitwidth } =>
      if bitwidth = 0 then none
      else some (scalarInfo ((bitwidth + 7) / 8) (spec.integerAlignment bitwidth))
  | .floatType type =>
      /- Floats have no entries of their own; their alignment is their natural one. -/
      if type.bitwidth = 0 then none
      else
        let size := (type.bitwidth + 7) / 8
        some (scalarInfo size (powerOfTwoCeil size))
  | .llvmPointerType _ =>
      some (scalarInfo spec.pointerSize spec.pointerAlignment)
  | .llvmArrayType { size, type } => do
      let element ← spec.query type
      some
        { size := element.allocSize * size
          abiAlignment := element.abiAlignment
          preferredAlignment := element.preferredAlignment }
  | .vectorType { shape, elementType } => do
      let element ← spec.query elementType
      /- As in LLVM, a vector is aligned to the next power of two of its size. -/
      let size := shape.foldl (· * ·) element.allocSize
      some (scalarInfo size (powerOfTwoCeil size))
  | _ => none

end DataLayoutSpec

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

/-- Build the query object for the given layout entries. -/
def ofSpec (spec : DataLayoutSpec) : DataLayout :=
  { query := spec.query }

end DataLayout

end

end Veir
