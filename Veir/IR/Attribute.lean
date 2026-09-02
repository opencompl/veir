module

import Veir.ForLean
public import Lean.Elab.Command
public import Std.Data.Iterators.Producers.Array

/-!
  # Attributes

  This file defines the `Attribute` data structure, which is an inductive type
  that can represent any compile-time information that can be stored in the IR.
  Attributes are used either as type annotations for SSA values, or as extra
  information stored in operations.

  The `TypeAttr` definition is a subtype of `Attribute` that carries the additional
  invariant that the attribute is a valid type annotation.

  `TypeAttr` corresponds to `mlir::Type`, and `Attribute`s that are not
  `TypeAttr`s correspond to an `mlir::Attribute` (as attributes and types are
  completely disjoint in MLIR). The reason for this lack of separation in VeIR is
  that merging both concepts into a single `Attribute` type allows to define
  functions that can work with both types and attributes without needing to define
  separate functions for each case. For instance, `mlir::AttrTypeWalker` can be
  defined for both `TypeAttr` and `Attribute` without needing to define separate
  walkers for each case. Similarly, `mlir::TypeAttr` is not needed, as we can
  store any `TypeAttr` as an `Attribute`.
-/

namespace Veir
public section

/--
  We print `ByteArray`s as UTF-8 strings, as all the `ByteArray`s we are manipulating are
  UTF-8 encoded strings.
-/
private local instance : Repr ByteArray where
  reprPrec ba _ := repr (String.fromUTF8! ba)

/-! ## Attribute definitions -/

/--
  A `!builtin.integer` is an integer type with a given bitwidth.
-/
structure IntegerType where
  bitwidth : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/--
 A floating point type with a given bitwidth.
-/
structure FloatType where
  bitwidth : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  A register type is an integer type with width 64.
-/
structure RegisterType where
  index: Option Nat := none
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  An integer literal with an associated integer type.
-/
structure IntegerAttr where
  value : Int
  type : IntegerType
deriving Inhabited, Repr, DecidableEq, Hashable

/--
 Floating point fastmath flags attribute.
-/
structure FastMathFlagsAttr where
  nnan : Bool
  ninf : Bool
  nsz : Bool
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  Arith integer overflow flags attribute.
-/
structure ArithIntegerOverflowFlagsAttr where
  nsw : Bool
  nuw : Bool
deriving Inhabited, Repr, DecidableEq, Hashable


/--
  LLVM calling convention attribute, e.g. `#llvm.cconv<ccc>`.
-/
structure CConvAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  LLVM linkage attribute, e.g. `#llvm.linkage<external>`.
-/
structure LinkageAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  LLVM frame pointer kind attribute, e.g. `#llvm.framePointerKind<all>`.
-/
structure FramePointerKindAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  LLVM unwind table kind attribute, e.g. `#llvm.uwtableKind<async>`.
-/
structure UwtableKindAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  LLVM tail call kind attribute, e.g. `#llvm.tailcallkind<none>`.
-/
structure TailCallKindAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  LLVM module flag attribute, e.g. `#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>`.
-/
structure ModuleFlagAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  LLVM target features attribute, e.g. `#llvm.target_features<["+cmov", "+sse"]>`.
-/
structure TargetFeaturesAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  DLTI data layout spec attribute, e.g. `#dlti.dl_spec<i64 = dense<64> : vector<2xi64>>`.
-/
structure DlSpecAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

structure RegisterAttr where
  value : Int
  type : RegisterType
deriving Inhabited, Repr, DecidableEq, Hashable

/--
A floating point attribute storing a Lean `Float` value with an associated float type.
-/
structure FloatAttr where
  value : Float
  type : FloatType
deriving Inhabited, Repr

/--
Temporary bridge lemma for deciding `FloatAttr` equality via `Float.toBits`.
-/
axiom floatEqOfToBitsEq {a b : Float} : a.toBits = b.toBits → a = b

instance : DecidableEq FloatAttr
  | a, b =>
    if hv : a.value.toBits = b.value.toBits then
      if ht : a.type = b.type then
        have hval : a.value = b.value := floatEqOfToBitsEq hv
        isTrue (by
          cases a
          cases b
          simp_all)
      else
        isFalse (by intro h; exact ht (congrArg FloatAttr.type h))
    else
      isFalse (by intro h; exact hv (congrArg (Float.toBits ∘ FloatAttr.value) h))

instance : Hashable FloatAttr where
  hash a := mixHash (hash a.value.toBits) (hash a.type)

/--
  An attribute containing a string.
  The string is stored as a `ByteArray` as unicode is not supported.
-/
structure StringAttr where
  value : ByteArray
deriving Inhabited, DecidableEq, Hashable

instance : Repr StringAttr where
  reprPrec attr _ := "StringAttr.mk " ++ repr (String.fromUTF8! attr.value)

/--
  A unit attribute that carries no information, but the information that it exists.
-/
structure UnitAttr where
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  A source location.
  This currently stores the raw string of the MLIR location syntax body.
-/
structure LocationAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  An array of integer attributes.
  The values are stored as an array of integers, and an associated integer type.
  Note that the integers are not necessarily in the range of the integer type.
-/
structure DenseArrayAttr where
  elementType : IntegerType
  values : Array Int
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  An array of dense elements, e.g., `!llvm.array<4 x i32>`.
  The values are stored as a string, and an associated type.
  The string is expected to be a valid MLIR representation of the array elements.
-/
structure DenseElementsAttr where
  value : String
  type : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  An attribute from an unknown dialect.
  It can be either a type attribute or a non-type attribute.
-/
structure UnregisteredAttr where
  value : String
  isType : Bool
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  A flat symbol reference attribute, e.g., `@foo` or `@"my.func"`.
  The value stores the raw text including the `@` prefix.
-/
structure FlatSymbolRefAttr where
  value : String
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The `!mod_arith.int` type from HEIR's modarith dialect.
-/
structure ModArithType where
  modulus : IntegerAttr
deriving Inhabited, Repr, DecidableEq, Hashable

/-- The bitwidth of the storage type of a `!mod_arith.int`. -/
public def ModArithType.bitwidth (ty : ModArithType) : Nat :=
  ty.modulus.type.bitwidth

namespace PDL

/--
  The `!pdl.operation` type, a handle to an `mlir::Operation` within a pattern.
-/
structure OperationType
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The `!pdl.value` type, a handle to an `mlir::Value` within a pattern.
-/
structure ValueType
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The `!pdl.type` type, a handle to an `mlir::Type` within a pattern.
-/
structure TypeType
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The `!pdl.attribute` type, a handle to an `mlir::Attribute` within a pattern.
-/
structure AttributeType
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The element of a `!pdl.range<...>`. MLIR restricts it to the four handle
  types, so a range never nests.
-/
inductive RangeElement
| attribute
| operation
| type
| value
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The `!pdl.range<...>` type, a handle to a range of PDL entities.
-/
structure RangeType where
  element : RangeElement
deriving Inhabited, Repr, DecidableEq, Hashable

end PDL

namespace LLVM

structure VoidType
deriving Inhabited, Repr, DecidableEq, Hashable

structure PointerType
deriving Inhabited, Repr, DecidableEq, Hashable

/--
 A byte type with a given bitwidth.
-/
structure ByteType where
  bitwidth : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

end LLVM

/-!
  # Cuda Tile types
-/

namespace CudaTile

/--
  An elemental pointer type represents a single location in global device memory.
  Pointers are typed, i.e., they carry the type they point to.
-/

structure PointerType where
  pointeeType : IntegerType
deriving Inhabited, Repr, DecidableEq, Hashable

end CudaTile

namespace HW

/--
  The `ModulePort::Direction` type from CIRCT's hw dialect.
  This represents the direction of a module port.
-/
inductive ModulePort.Direction
| input
| output
| inout
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The `ModulePort` type from CIRCT's hw dialect.
  This represents a port to a module with a direction, type and name.
-/
structure ModulePort where
  name : String
  type : IntegerType
  dir : ModulePort.Direction
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The `!hw.modty` type from CIRCT's hw dialect.
  This represents a list of ports to a module.
-/
structure ModuleType where
  ports : Array ModulePort
deriving Inhabited, Repr, DecidableEq, Hashable

end HW

mutual

/--
  The signature of a function, consisting of an array of input attributes
  and an array of output attributes.
-/
structure FunctionType where
  inputs : Array Attribute
  outputs : Array Attribute
  isVarArg : Bool := false
deriving Inhabited, Repr, Hashable

/--
  The payload of an LLVM function type attribute.

  This wrapper distinguishes `!llvm.func` types from builtin function types at
  the Lean type level while reusing their common representation.
-/
structure LLVMFunctionType where
  functionType : FunctionType
deriving Inhabited, Repr, Hashable

/--
  An attribute that holds a sequence of attributes.
-/
structure ArrayAttr where
  value : Array Attribute
deriving Inhabited, Repr, Hashable

/--
  A dictionary attribute that maps byte array keys to attribute values.
-/
structure DictionaryAttr where
  /--
    Entries are encoded as an array to allow decidable equality and iteration, which is
    not possible with either a `HashMap` or an `ExtHashMap`.
    Entries are expected to be sorted by key and each key is unique, so that we can use a
    binary search and have O(log(n)) lookup time. This invariant is not enforced proof-wise but
    is expected to be maintained at all time.
  -/
  entries : Array (ByteArray × Attribute)
  /- TODO: figure out how to maintain a proof of sorted-ness and uniqueness. -/
deriving Inhabited, Repr, Hashable

/--
  An attribute representing a fixed-sized array type
-/
structure LLVM.ArrayType where
  size : Nat
  type : Attribute
deriving Repr, Hashable

/--
  The `!match.optional<...>` type, wrapping a PDL handle type whose value may
  be null at match time.

  Navigation in the `match` dialect that can fail returns one of these, and
  `match.is_not_null` is the only way back to the bare handle. The wrapped type
  is an arbitrary attribute rather than a fixed enumeration because MLIR places
  no restriction on it beyond it being a type; the verifier narrows it.
-/
structure Match.OptionalType where
  innerType : Attribute
deriving Repr, Hashable

/--
  A data structure that represents compile-time information in the IR.
  Attributes are used either as type annotations for SSA values, or
  as extra information stored in operations.
-/
inductive Attribute
/-- Integer type -/
| integerType (type : IntegerType)
/-- Float type -/
| floatType (type : FloatType)
/-- Integer attribute -/
| integerAttr (attr : IntegerAttr)
/-- Float attribute -/
| floatAttr (attr : FloatAttr)
/-- Float fast math flags attribute -/
| fastMathFlagsAttr (attr : FastMathFlagsAttr)
/-- Arith integer overflow flags attribute -/
| arithIntegerOverflowFlagsAttr (attr : ArithIntegerOverflowFlagsAttr)
/-- LLVM calling convention attribute -/
| cconvAttr (attr : CConvAttr)
/-- LLVM linkage attribute -/
| linkageAttr (attr : LinkageAttr)
/-- LLVM frame pointer kind attribute -/
| framePointerKindAttr (attr : FramePointerKindAttr)
/-- LLVM unwind table kind attribute -/
| uwtableKindAttr (attr : UwtableKindAttr)
/-- LLVM tail call kind attribute -/
| tailCallKindAttr (attr : TailCallKindAttr)
/-- LLVM module flag attribute -/
| moduleFlagAttr (attr : ModuleFlagAttr)
/-- LLVM target features attribute -/
| targetFeaturesAttr (attr : TargetFeaturesAttr)
/-- DLTI data layout spec attribute -/
| dlSpecAttr (attr : DlSpecAttr)
/-- Register type -/
| registerType (type : RegisterType)
/-- Register attribute -/
| registerAttr (attr : RegisterAttr)
/-- String attribute -/
| stringAttr (attr : StringAttr)
/-- Unit attribute -/
| unitAttr (attr : UnitAttr)
/-- Location attribute -/
| locationAttr (attr : LocationAttr)
/-- Array attribute -/
| arrayAttr (attr : ArrayAttr)
/-- Dense array attribute -/
| denseArrayAttr (attr : DenseArrayAttr)
/-- Dense elements attribute -/
| denseElementsAttr (attr : DenseElementsAttr)
/-- Dictionary attribute -/
| dictionaryAttr (attr : DictionaryAttr)
/-- Function type -/
| functionType (type : FunctionType)
/-- An attribute from an unknown dialect. -/
| unregisteredAttr (attr : UnregisteredAttr)
/-- A flat symbol reference, e.g., `@foo` or `@"my.func"`. -/
| flatSymbolRefAttr (attr : FlatSymbolRefAttr)
/-- HEIR modarith type -/
| modArithType (type : ModArithType)
/-- LLVM void type -/
| llvmVoidType (type : LLVM.VoidType)
/-- LLVM byte type -/
| byteType (type : LLVM.ByteType)
/-- LLVM pointer type -/
| llvmPointerType (type : LLVM.PointerType)
/-- LLVM array type -/
| llvmArrayType (type : LLVM.ArrayType)
/-- LLVM function type -/
| llvmFunctionType (type : LLVMFunctionType)
/-- Cuda Tile pointer type -/
| cudaTilePointerType (type : CudaTile.PointerType)
/-- CIRCT hw module type -/
| hwModuleType (type : HW.ModuleType)
/-- PDL range handle type -/
| pdlRangeType (type : PDL.RangeType)
/-- PDL attribute handle type -/
| pdlAttributeType (type : PDL.AttributeType)
/-- PDL operation handle type -/
| pdlOperationType (type : PDL.OperationType)
/-- PDL value handle type -/
| pdlValueType (type : PDL.ValueType)
/-- PDL type handle type -/
| pdlTypeType (type : PDL.TypeType)
/-- Match optional handle type -/
| matchOptionalType (type : Match.OptionalType)
deriving Inhabited, Repr, Hashable

end

instance : Coe FunctionType LLVMFunctionType where
  coe := .mk

instance : Coe LLVMFunctionType FunctionType where
  coe := LLVMFunctionType.functionType

instance : Inhabited LLVM.ArrayType where
  default := { size := 0, type := .llvmPointerType .mk }

instance : Inhabited Match.OptionalType where
  default := { innerType := .pdlValueType .mk }

def ArrayAttr.empty : ArrayAttr := { value := #[] }

/--
  Construct a `DictionaryAttr` from an array of key-value pairs.
  TODO: ensure that entries are unique.
-/
def DictionaryAttr.fromArray (entries : Array (ByteArray × Attribute)) : DictionaryAttr :=
  { entries := entries.insertionSort (fun entry1 entry2 => (compare entry1.1 entry2.1).isLT) }

def DictionaryAttr.empty : DictionaryAttr := { entries := #[] }

theorem FunctionType.sizeOf_elems_inputs {ft : FunctionType} (hx : x ∈ ft.inputs) :
    sizeOf x < sizeOf ft := by
  grind [Array.sizeOf_lt_of_mem hx, cases FunctionType]

theorem FunctionType.sizeOf_elems_outputs {ft : FunctionType} (hx : x ∈ ft.outputs) :
    sizeOf x < sizeOf ft := by
  grind [Array.sizeOf_lt_of_mem hx, cases FunctionType]

theorem LLVMFunctionType.sizeOf_functionType {ft : LLVMFunctionType} :
    sizeOf ft.functionType < sizeOf ft := by
  grind [cases LLVMFunctionType]

theorem ArrayAttr.sizeOf_elems_value {aa : ArrayAttr} (hx : x ∈ aa.value) :
    sizeOf x < sizeOf aa := by
  grind [Array.sizeOf_lt_of_mem hx, cases ArrayAttr]

theorem DictionaryAttr.sizeOf_elems_entries {da : DictionaryAttr} (hx : x ∈ da.entries) :
    sizeOf x < sizeOf da := by
  grind [Array.sizeOf_lt_of_mem hx, cases DictionaryAttr]

theorem LLVM.ArrayType.sizeOf_elems_type {t : ArrayType} :
    sizeOf t.type < sizeOf t := by
  grind [cases ArrayType]

theorem Match.OptionalType.sizeOf_innerType {t : Match.OptionalType} :
    sizeOf t.innerType < sizeOf t := by
  grind [cases Match.OptionalType]

/-!
  ## DecidableEq instances
-/

mutual
def FunctionType.decEq (type1 type2 : FunctionType) : Decidable (type1 = type2) :=
  let inputs1 := type1.inputs
  let outputs1 := type1.outputs
  let inputs2 := type2.inputs
  let outputs2 := type2.outputs
  match Array.instDecidabelEq' inputs1 inputs2 (fun x y _ _ => Attribute.decEq x y) with
  | isTrue _ =>
    match Array.instDecidabelEq' outputs1 outputs2 (fun x y _ _ => Attribute.decEq x y) with
    | isTrue _ =>
      if h : type1.isVarArg = type2.isVarArg then
        isTrue (by grind [cases FunctionType])
      else
        isFalse (by grind)
    | isFalse _ => isFalse (by grind)
  | isFalse _ => isFalse (by grind)
termination_by sizeOf type1
decreasing_by
  · have := @FunctionType.sizeOf_elems_inputs
    grind
  · have := @FunctionType.sizeOf_elems_outputs
    grind

def LLVMFunctionType.decEq (type1 type2 : LLVMFunctionType) : Decidable (type1 = type2) :=
  match FunctionType.decEq type1.functionType type2.functionType with
  | isTrue _ => isTrue (by grind [cases LLVMFunctionType])
  | isFalse _ => isFalse (by grind)
termination_by sizeOf type1
decreasing_by
  apply LLVMFunctionType.sizeOf_functionType

def ArrayAttr.decEq (arr1 arr2 : ArrayAttr) : Decidable (arr1 = arr2) :=
  let value1 := arr1.value
  let value2 := arr2.value
  match Array.instDecidabelEq' value1 value2 (fun x y _ _ => x.decEq y) with
  | isTrue _ => isTrue (by grind [cases ArrayAttr])
  | isFalse _ => isFalse (by grind)
termination_by sizeOf arr1
decreasing_by
  have := @ArrayAttr.sizeOf_elems_value
  grind

def LLVM.ArrayType.decEq (arr1 arr2 : LLVM.ArrayType) : Decidable (arr1 = arr2) :=
  let size1 := arr1.size
  let size2 := arr2.size
  let type1 := arr1.type
  let type2 := arr2.type
  match Int.instDecidableEq size1 size2 with
  | isTrue _ =>
    match Attribute.decEq type1 type2 with
    | isTrue _ => isTrue (by grind [cases LLVM.ArrayType])
    | isFalse _ => isFalse (by grind)
  | isFalse _ => isFalse (by grind)

termination_by sizeOf arr1
decreasing_by
  have := @LLVM.ArrayType.sizeOf_elems_type
  grind

def Match.OptionalType.decEq (opt1 opt2 : Match.OptionalType) : Decidable (opt1 = opt2) :=
  match Attribute.decEq opt1.innerType opt2.innerType with
  | isTrue _ => isTrue (by grind [cases Match.OptionalType])
  | isFalse _ => isFalse (by grind)
termination_by sizeOf opt1
decreasing_by
  have := @Match.OptionalType.sizeOf_innerType
  grind

def DictionaryAttr.decEq (dict1 dict2 : DictionaryAttr) : Decidable (dict1 = dict2) :=
  let entries1 := dict1.entries
  let entries2 := dict2.entries
  match Array.instDecidabelEq' entries1 entries2 fun ⟨k₁, v₁⟩ ⟨k₂, v₂⟩ hx hy =>
    if _ : k₁ = k₂ then
      match v₁.decEq v₂ with
      | isTrue _ => isTrue (by grind)
      | isFalse _ => isFalse (by grind)
    else isFalse (by grind)
  with
  | isTrue _ => isTrue (by grind [cases DictionaryAttr])
  | isFalse _ => isFalse (by grind)
termination_by sizeOf dict1
decreasing_by
  have := @DictionaryAttr.sizeOf_elems_entries
  grind
def Attribute.decEq (attr1 attr2 : Attribute) : Decidable (attr1 = attr2) := by
  cases h1 : attr1 <;> cases h2 : attr2
  case integerType.integerType type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case floatType.floatType type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case byteType.byteType type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case fastMathFlagsAttr.fastMathFlagsAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case cconvAttr.cconvAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case linkageAttr.linkageAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case framePointerKindAttr.framePointerKindAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case uwtableKindAttr.uwtableKindAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case tailCallKindAttr.tailCallKindAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case moduleFlagAttr.moduleFlagAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case targetFeaturesAttr.targetFeaturesAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case dlSpecAttr.dlSpecAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case unregisteredAttr.unregisteredAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case functionType.functionType type1 type2 =>
    exact (match FunctionType.decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case dictionaryAttr.dictionaryAttr attr1 attr2 =>
    exact (match DictionaryAttr.decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case integerAttr.integerAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case floatAttr.floatAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case arithIntegerOverflowFlagsAttr.arithIntegerOverflowFlagsAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case stringAttr.stringAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case unitAttr.unitAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case locationAttr.locationAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case arrayAttr.arrayAttr attr1 attr2 =>
    exact (match ArrayAttr.decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case modArithType.modArithType type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case registerType.registerType type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case registerAttr.registerAttr type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case llvmVoidType.llvmVoidType type1 type2 =>
    exact (isTrue (by grind))
  case llvmPointerType.llvmPointerType type1 type2 =>
    exact (isTrue (by grind))
  case llvmArrayType.llvmArrayType type1 type2 =>
    exact (match LLVM.ArrayType.decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case llvmFunctionType.llvmFunctionType type1 type2 =>
    exact (match LLVMFunctionType.decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case cudaTilePointerType.cudaTilePointerType type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case denseElementsAttr.denseElementsAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case denseArrayAttr.denseArrayAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case flatSymbolRefAttr.flatSymbolRefAttr attr1 attr2 =>
    exact (match decEq attr1 attr2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case hwModuleType.hwModuleType type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case pdlRangeType.pdlRangeType type1 type2 =>
    exact (match decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case matchOptionalType.matchOptionalType type1 type2 =>
    exact (match Match.OptionalType.decEq type1 type2 with
      | isTrue hEq => isTrue (by grind)
      | isFalse hEq => isFalse (by grind))
  case pdlAttributeType.pdlAttributeType type1 type2 =>
    exact (isTrue (by grind))
  case pdlOperationType.pdlOperationType type1 type2 =>
    exact (isTrue (by grind))
  case pdlValueType.pdlValueType type1 type2 =>
    exact (isTrue (by grind))
  case pdlTypeType.pdlTypeType type1 type2 =>
    exact (isTrue (by grind))
  all_goals exact isFalse (by grind)
termination_by sizeOf attr1
end

instance : DecidableEq Attribute := Attribute.decEq
instance : DecidableEq FunctionType := FunctionType.decEq
instance : DecidableEq LLVMFunctionType := LLVMFunctionType.decEq
instance : DecidableEq ArrayAttr := ArrayAttr.decEq
instance : DecidableEq DictionaryAttr := DictionaryAttr.decEq

/-!
  ## ToString implementation

  `ToString` is used to convert attributes to their MLIR textual representation.
  It is also the syntax used for printing attributes in the REPL and in error messages.
-/

instance : ToString IntegerType where
  toString type := s!"i{type.bitwidth}"

instance : ToString FloatType where
  toString type := s!"f{type.bitwidth}"

instance : ToString LLVM.ByteType where
  toString type := s!"!llvm.byte<{type.bitwidth}>"

instance : ToString FastMathFlagsAttr where
  toString type := Id.run do
    let mut array : List String := []
    if type.nnan && type.ninf && type.nsz then array := array ++ ["fast"]
    else
      if type.nnan then array := array ++ ["nnan"]
      if type.ninf then array := array ++ ["ninf"]
      if type.nsz then array := array ++ ["nsz"]
      if !type.nnan && !type.ninf && !type.nsz then array := array ++ ["none"]
    s!"#llvm.fastmath<{String.intercalate ", " array}>"

def integerOverflowFlagsString (dialect : String) (nsw nuw : Bool) : String :=
  let flags :=
    if nsw && nuw then ["nsw", "nuw"]
    else if nsw then ["nsw"]
    else if nuw then ["nuw"]
    else ["none"]
  s!"#{dialect}.overflow<{String.intercalate ", " flags}>"

instance : ToString ArithIntegerOverflowFlagsAttr where
  toString attr := integerOverflowFlagsString "arith" attr.nsw attr.nuw

instance : ToString CConvAttr where
  toString attr := s!"#llvm.cconv<{attr.value}>"

instance : ToString LinkageAttr where
  toString attr := s!"#llvm.linkage<{attr.value}>"

instance : ToString FramePointerKindAttr where
  toString attr := s!"#llvm.framePointerKind<{attr.value}>"

instance : ToString UwtableKindAttr where
  toString attr := s!"#llvm.uwtableKind<{attr.value}>"

instance : ToString TailCallKindAttr where
  toString attr := s!"#llvm.tailcallkind<{attr.value}>"

instance : ToString ModuleFlagAttr where
  toString attr := s!"#llvm.mlir.module_flag<{attr.value}>"

instance : ToString TargetFeaturesAttr where
  toString attr := s!"#llvm.target_features<{attr.value}>"

instance : ToString DlSpecAttr where
  toString attr := s!"#dlti.dl_spec<{attr.value}>"

instance : ToString IntegerAttr where
  toString attr := s!"{attr.value} : {attr.type}"

instance : ToString FloatAttr where
  toString attr := s!"{attr.value} : {attr.type}"

instance : ToString RegisterType where
  toString type :=
    match type.index with
    | none => s!"!riscv.reg"
    | some i => s!"!riscv.reg<x{i}>"

instance : ToString RegisterAttr where
  toString attr := s!"{attr.value} : !riscv.reg"

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (n.toNat + '0'.toNat)
  else Char.ofNat (n.toNat - 10 + 'A'.toNat)

def escapeStringLiteral (b : ByteArray) : String := Id.run do
  let mut result := ""
  for byte in b do
    if byte == '\\'.toUInt8 then result := result ++ "\\\\"
    else if byte == '"'.toUInt8 then result := result ++ "\\\""
    else if byte == '\n'.toUInt8 then result := result ++ "\\n"
    else if byte == '\t'.toUInt8 then result := result ++ "\\t"
    else if byte >= 0x20 && byte < 0x7F then result := result.push (Char.ofNat byte.toNat)
    else
      /- LLVM convention: encode hex as \HH. -/
      result := result.push '\\'
      result := result.push (hexDigit (byte >>> 4))
      result := result.push (hexDigit (byte &&& 0x0F))
  return result

instance : ToString StringAttr where
  toString attr := s!"\"{escapeStringLiteral attr.value}\""

instance : ToString UnitAttr where
  toString _ := "unit"

instance : ToString LocationAttr where
  toString attr := s!"loc(" ++ attr.value ++ ")"

instance : ToString DenseArrayAttr where
  toString attr :=
    let values := if attr.values.isEmpty then ""
      else ": " ++ String.intercalate ", " (attr.values.toList.map ToString.toString)
    s!"array<{attr.elementType}{values}>"

instance : ToString DenseElementsAttr where
  toString attr := s!"dense<{attr.value}> : {attr.type}"

instance : ToString UnregisteredAttr where
  toString attr := attr.value

instance : ToString FlatSymbolRefAttr where
  toString attr := attr.value

instance : ToString ModArithType where
  toString type := s!"!mod_arith.int<{type.modulus}>"

instance : ToString PDL.RangeElement where
  toString element :=
    match element with
    | .attribute => "attribute"
    | .operation => "operation"
    | .type => "type"
    | .value => "value"

instance : ToString PDL.RangeType where
  toString type := s!"!pdl.range<{type.element}>"

instance : ToString PDL.AttributeType where
  toString _ := "!pdl.attribute"

instance : ToString PDL.OperationType where
  toString _ := "!pdl.operation"

instance : ToString PDL.ValueType where
  toString _ := "!pdl.value"

instance : ToString PDL.TypeType where
  toString _ := "!pdl.type"

instance : ToString LLVM.VoidType where
  toString _ := "!llvm.void"

instance : ToString LLVM.PointerType where
  toString _ := "!llvm.ptr"

instance : ToString CudaTile.PointerType where
  toString ptr := s!"!cuda_tile.ptr<{ptr.pointeeType}>"

instance : ToString HW.ModulePort.Direction where
  toString
  | .input => "input"
  | .output => "output"
  | .inout => "inout"

instance : ToString HW.ModulePort where
  toString attr := s!"{attr.dir} {attr.name} : {attr.type}"

instance : ToString HW.ModuleType where
  toString attr :=
    let values := attr.ports.iter.map ToString.toString |>.intercalateString ", "
    s!"!hw.modty<{values}>"

mutual

def ArrayAttr.toString (attr : ArrayAttr) : String :=
  let elems := String.intercalate ", " (attr.value.toList.map Attribute.toString)
  s!"[{elems}]"
termination_by sizeOf attr
decreasing_by
  apply ArrayAttr.sizeOf_elems_value
  grind

def DictionaryAttr.entryToString (entry : ByteArray × Attribute) : String :=
  let key := String.fromUTF8! entry.1
  match entry.2 with
  | .unitAttr _ => key
  | _ => s!"\"{key}\" = {Attribute.toString entry.2}"
termination_by sizeOf entry
decreasing_by grind

def DictionaryAttr.toString (attr : DictionaryAttr) : String :=
  let entries := attr.entries.toList.map DictionaryAttr.entryToString
  s!"\{{String.intercalate ", " entries}}"
termination_by sizeOf attr
decreasing_by
  rename_i entry _
  have : entry ∈ attr.entries := by grind
  grind [Array.sizeOf_lt_of_mem this, cases DictionaryAttr]

def FunctionType.toLLVMString (type : FunctionType) : String :=
  let paramStrs := type.inputs.toList.map Attribute.toString
  let paramStrs := if type.isVarArg then paramStrs ++ ["..."] else paramStrs
  let params := String.intercalate ", " paramStrs
  let result := match _ : type.outputs.size with
    | 1 =>
      match type.outputs[0] with
      | .llvmVoidType _ => "void"
      | _ => Attribute.toString type.outputs[0]
    | _ => "<invalid>"
  s!"!llvm.func<{result} ({params})>"
termination_by sizeOf type
decreasing_by
  · apply FunctionType.sizeOf_elems_inputs
    grind
  · apply FunctionType.sizeOf_elems_outputs
    grind

def LLVMFunctionType.toString (type : LLVMFunctionType) : String :=
  type.functionType.toLLVMString
termination_by sizeOf type
decreasing_by
  apply LLVMFunctionType.sizeOf_functionType

def FunctionType.toString (type : FunctionType) : String :=
  let inputs := String.intercalate ", " (type.inputs.toList.map Attribute.toString)
  let outputs := match _ : type.outputs.size with
  | 0 => "()"
  | 1 =>
    match _ : type.outputs[0] with
    | .functionType _ => s!"({type.outputs[0].toString})"
    | output => output.toString
  | _ =>
    s!"({String.intercalate ", " (type.outputs.toList.map Attribute.toString)})"
  s!"({inputs}) -> {outputs}"
termination_by sizeOf type
decreasing_by
  · apply FunctionType.sizeOf_elems_inputs
    grind
  · apply FunctionType.sizeOf_elems_outputs
    grind
  · apply FunctionType.sizeOf_elems_outputs
    grind
  · apply FunctionType.sizeOf_elems_outputs
    grind

def LLVM.ArrayType.toString (type : LLVM.ArrayType) : String :=
  s!"!llvm.array<{type.size} x {Attribute.toString type.type}>"
termination_by sizeOf type
decreasing_by
  apply LLVM.ArrayType.sizeOf_elems_type

def Match.OptionalType.toString (type : Match.OptionalType) : String :=
  s!"!match.optional<{Attribute.toString type.innerType}>"
termination_by sizeOf type
decreasing_by
  apply Match.OptionalType.sizeOf_innerType

/--
  Convert an attribute to a string representation.
-/
def Attribute.toString (attr : Attribute) : String :=
  match attr with
  | .integerType type => ToString.toString type
  | .floatType type => ToString.toString type
  | .byteType type => ToString.toString type
  | .fastMathFlagsAttr attr => ToString.toString attr
  | .arithIntegerOverflowFlagsAttr attr => ToString.toString attr
  | .cconvAttr attr => ToString.toString attr
  | .linkageAttr attr => ToString.toString attr
  | .framePointerKindAttr attr => ToString.toString attr
  | .uwtableKindAttr attr => ToString.toString attr
  | .tailCallKindAttr attr => ToString.toString attr
  | .moduleFlagAttr attr => ToString.toString attr
  | .targetFeaturesAttr attr => ToString.toString attr
  | .dlSpecAttr attr => ToString.toString attr
  | .integerAttr attr => ToString.toString attr
  | .floatAttr attr => ToString.toString attr
  | .registerType type => ToString.toString type
  | .registerAttr attr => ToString.toString attr
  | .stringAttr attr => ToString.toString attr
  | .unitAttr attr => ToString.toString attr
  | .locationAttr attr => ToString.toString attr
  | .arrayAttr attr => attr.toString
  | .denseElementsAttr attr => ToString.toString attr
  | .denseArrayAttr attr => ToString.toString attr
  | .dictionaryAttr attr => attr.toString
  | .unregisteredAttr attr => ToString.toString attr
  | .flatSymbolRefAttr attr => ToString.toString attr
  | .functionType type => type.toString
  | .modArithType type => ToString.toString type
  | .llvmVoidType type => ToString.toString type
  | .llvmPointerType type => ToString.toString type
  | .llvmArrayType type => type.toString
  | .llvmFunctionType type => type.toString
  | .cudaTilePointerType type => ToString.toString type
  | .hwModuleType type => ToString.toString type
  | .pdlRangeType type => ToString.toString type
  | .pdlAttributeType type => ToString.toString type
  | .pdlOperationType type => ToString.toString type
  | .pdlValueType type => ToString.toString type
  | .pdlTypeType type => ToString.toString type
  | .matchOptionalType type => type.toString
termination_by sizeOf attr

end

instance : ToString Attribute where
  toString := Attribute.toString

instance : ToString FunctionType where
  toString := FunctionType.toString

instance : ToString LLVMFunctionType where
  toString := LLVMFunctionType.toString

instance : ToString ArrayAttr where
  toString := ArrayAttr.toString

instance : ToString DictionaryAttr where
  toString := DictionaryAttr.toString

instance : ToString LLVM.ArrayType where
  toString := LLVM.ArrayType.toString

instance : ToString Match.OptionalType where
  toString := Match.OptionalType.toString

/-! ## Attribute Subtype Interface -/

/--
`IsAttr Attr` states that `Attr` is represented by a subset of `Attribute`.

It defines an injection from the attribute-specific type to `Attribute` and a
partial projection back to that type. Every attribute-specific type is also
printable and inhabited.
-/
class IsAttr (Attr : Type) extends ToString Attr, Inhabited Attr where
  /-- The name of the attribute type. -/
  name : String
  /-- Embed an attribute-specific value into `Attribute`. -/
  inject : Attr → Attribute
  /-- Project an `Attribute` to the attribute-specific type, when possible. -/
  project : Attribute → Option Attr
  /-- The projection recognizes exactly the values produced by the injection. -/
  project_eq_some_iff (attr : Attribute) (specificAttr : Attr) :
    project attr = some specificAttr ↔ inject specificAttr = attr

attribute [grind unfold] IsAttr.inject

namespace Attribute

/--
Try to cast an attribute to a concrete attribute type.

This is equivalent to `mlir::dyn_cast<Attr>(attr)` in MLIR.
-/
@[inline]
def cast? (attr : Attribute) (Attr : Type) [IsAttr Attr] : Option Attr :=
  IsAttr.project attr

/-- Try to cast an attribute to a concrete attribute type, and throw an error if the cast fails. -/
@[inline]
def cast! (attr : Attribute) (Attr : Type) [IsAttr Attr] : Attr :=
  match cast? attr Attr with
  | some specificAttr => specificAttr
  | none =>
    panic! s!"Attribute.cast!: attribute {attr} is not of the expected type {IsAttr.name Attr}."

/--
Check if an attribute is of a specific type.

This is equivalent to `mlir::isa<Attr>(attr)` in MLIR.
-/
@[inline]
def isa (attr : Attribute) (Attr : Type) [IsAttr Attr] : Bool :=
  match attr.cast? Attr with
  | some _ => true
  | none => false

/--
Cast an attribute to a concrete attribute type, assuming it is of the expected type.

This is equivalent to `mlir::cast<Attr>(attr)` in MLIR.
-/
@[inline]
def cast (attr : Attribute) (Attr : Type) [IsAttr Attr] (h : attr.isa Attr) : Attr :=
  (attr.cast? Attr).get (by grind [isa, cast?])

/-- Create an attribute from a concrete attribute type. -/
@[inline, expose, grind unfold]
def of (Attr : Type) [IsAttr Attr] (specificAttr : Attr) : Attribute :=
  IsAttr.inject specificAttr

/-- Coercion from attribute-specific type to `Attribute`. -/
instance CoeHead (Attr : Type) [IsAttr Attr] : CoeHead Attr Attribute where
  coe := Attribute.of Attr

end Attribute

namespace IsAttr

variable {Attr : Type} [IsAttr Attr]

@[simp, grind =]
theorem cast?_of (specificAttr : Attr) :
    (Attribute.of Attr specificAttr).cast? Attr = some specificAttr := by
  simp [Attribute.of, Attribute.cast?, IsAttr.project_eq_some_iff]

theorem of_injective : Function.Injective (Attribute.of Attr) := by
  intro attr₁ attr₂ h
  grind [congrArg (Attribute.cast? · Attr) h]

@[simp]
theorem cast?_eq_some_iff (attr : Attribute) (specificAttr : Attr) :
    attr.cast? Attr = some specificAttr ↔ Attribute.of Attr specificAttr = attr := by
  grind [IsAttr.project_eq_some_iff, Attribute.of, Attribute.cast?]

grind_pattern cast?_eq_some_iff =>
  attr.cast? Attr, Attribute.of Attr specificAttr

@[simp, grind =]
theorem isa_of (specificAttr : Attr) :
    (Attribute.of Attr specificAttr).isa Attr := by
  simp [Attribute.isa]

@[simp, grind =]
theorem cast!_of (specificAttr : Attr) :
    (Attribute.of Attr specificAttr).cast! Attr = specificAttr := by
  simp [Attribute.cast!]

@[simp, grind =]
theorem cast_of (specificAttr : Attr)
    (h : (Attribute.of Attr specificAttr).isa Attr) :
    (Attribute.of Attr specificAttr).cast Attr h = specificAttr := by
  simp [Attribute.cast]

@[simp, grind =]
theorem of_cast (attr : Attribute) (h : attr.isa Attr) :
    Attribute.of Attr (attr.cast Attr h) = attr := by
  simp only [Attribute.cast, Attribute.of]
  grind [Attribute.isa, Attribute.cast?, IsAttr.project_eq_some_iff]

end IsAttr

/--
Generate an `IsAttr` instance for an `Attribute` constructor with one payload.

For example, `attribute_instance IntegerType => Attribute.integerType` generates
the inherited printing and inhabitation operations, the injection, and the
constructor-discriminating partial projection.
-/
syntax "attribute_instance " term " => " ident : command

macro_rules
  | `(attribute_instance $attrType:term => $ctor:ident) => do
    let attrName := Lean.Syntax.mkStrLit (toString attrType)
    `(@[expose] instance : IsAttr $attrType where
        toString := ToString.toString
        default := Inhabited.default
        name := $attrName
        inject := $ctor
        project
          | $ctor value => some value
          | _ => none
        project_eq_some_iff attr _ := by
          cases attr <;> simp_all [eq_comm])

open Lean Elab Command Meta

/--
Generate an `IsAttr` instance for every single-payload constructor of an
attribute inductive.
-/
elab "#generate_attribute_instances" attrInductive:ident : command => do
  let attributeName ← resolveGlobalConstNoOverload attrInductive
  let env ← getEnv
  let some (.inductInfo info) := env.find? attributeName
    | throwError m!"Type {attributeName} is not defined or not an inductive."
  for ctorName in info.ctors do
    let some (.ctorInfo ctorInfo) := env.find? ctorName
      | throwError m!"Constructor {ctorName} is not defined."
    let .forallE _ (.const attrTypeName _) resultType _ := ctorInfo.type
      | throwError m!"Constructor {ctorName} must have exactly one attribute payload."
    unless resultType.isConstOf attributeName do
      throwError m!"Constructor {ctorName} does not construct {attributeName}."
    elabCommand <| ←
      `(attribute_instance $(mkIdent attrTypeName) => $(mkIdent ctorName))

instance : IsAttr Attribute where
  toString := Attribute.toString
  default := Inhabited.default
  name := "Attribute"
  inject := id
  project := some
  project_eq_some_iff _ _ := by grind

#generate_attribute_instances Attribute

/-!
  ## TypeAttr definition

  `TypeAttr` is defined as a subtype of `Attribute` that carries the additional invariant
  that the attribute is a valid type annotation (i.e., `isType` is true).
-/

namespace Attribute

/--
  Determine if an attribute can be used as a type annotation for SSA
  values.
-/
def isType (attr : Attribute) : Bool :=
  match attr with
  | .integerType _ => true
  | .floatType _ => true
  | .byteType _ => true
  | .fastMathFlagsAttr _ => false
  | .arithIntegerOverflowFlagsAttr _ => false
  | .cconvAttr _ => false
  | .linkageAttr _ => false
  | .framePointerKindAttr _ => false
  | .uwtableKindAttr _ => false
  | .tailCallKindAttr _ => false
  | .moduleFlagAttr _ => false
  | .targetFeaturesAttr _ => false
  | .dlSpecAttr _ => false
  | .integerAttr _ => false
  | .floatAttr _ => false
  | .stringAttr _ => false
  | .unitAttr _ => false
  | .locationAttr _ => false
  | .arrayAttr _ => false
  | .denseArrayAttr _ => false
  | .denseElementsAttr _ => false
  | .dictionaryAttr _ => false
  | .unregisteredAttr attr => attr.isType
  | .flatSymbolRefAttr _ => false
  | .functionType _ => true
  | .modArithType _ => true
  | .registerType _ => true
  | .registerAttr _ => false
  | .llvmVoidType _ => true
  | .llvmPointerType _ => true
  | .llvmArrayType _ => true
  | .llvmFunctionType _ => true
  | .cudaTilePointerType _ => true
  | .hwModuleType _ => true
  | .pdlRangeType _ => true
  | .pdlAttributeType _ => true
  | .pdlOperationType _ => true
  | .pdlValueType _ => true
  | .pdlTypeType _ => true
  | .matchOptionalType _ => true

/--
  Returns the size, in bits, that an LLVM type would use if stored to memory.
-/
def bitwidthOfType (type : Attribute) : Option Nat :=
  match type with
  | .integerType { bitwidth } | .floatType { bitwidth } | .byteType { bitwidth } => some bitwidth
  | .llvmPointerType _ => some 64
  | _ => none

/--
  Returns the size, in bytes, that an LLVM type would use if stored to memory.
-/
def sizeOfType (type : Attribute) : Option Nat :=
  match type with
  | .integerType { bitwidth } | .floatType { bitwidth } | .byteType { bitwidth } => some ((bitwidth + 7) / 8)
  | .llvmPointerType _ => some 8
  | .llvmArrayType { size, type } => do
      let inner ← sizeOfType type
      some (inner * size)
  | _ => none

@[simp, grind =]
theorem isType_integerType type : (integerType type).isType = true := by rfl
@[simp, grind =]
theorem isType_floatType type : (floatType type).isType = true := by rfl
@[simp, grind =]
theorem isType_byteType type : (byteType type).isType = true := by rfl
@[simp, grind =]
theorem isType_fastMathFlags flags : (fastMathFlagsAttr flags).isType = false := by rfl
@[simp, grind =]
theorem isType_cconv attr : (cconvAttr attr).isType = false := by rfl
@[simp, grind =]
theorem isType_linkage attr : (linkageAttr attr).isType = false := by rfl
@[simp, grind =]
theorem isType_framePointerKind attr : (framePointerKindAttr attr).isType = false := by rfl
@[simp, grind =]
theorem isType_uwtableKind attr : (uwtableKindAttr attr).isType = false := by rfl
@[simp, grind =]
theorem isType_tailCallKind attr : (tailCallKindAttr attr).isType = false := by rfl
@[simp, grind =]
theorem isType_moduleFlag attr : (moduleFlagAttr attr).isType = false := by rfl
@[simp, grind =]
theorem isType_targetFeatures attr : (targetFeaturesAttr attr).isType = false := by rfl
@[simp, grind =]
theorem isType_dlSpec attr : (dlSpecAttr attr).isType = false := by rfl
@[simp, grind =]
theorem isType_unregistered unregistered :
  (unregisteredAttr unregistered).isType = unregistered.isType := by rfl
@[simp, grind =]
theorem isType_functionType type : (functionType type).isType = true := by rfl
@[simp, grind =]
theorem isType_modArithType type : (modArithType type).isType = true := by rfl
@[simp, grind =]
theorem isType_registerType type : (registerType type).isType = true := by rfl
@[simp, grind =]
theorem isType_llvmVoidType type : (llvmVoidType type).isType = true := by rfl
@[simp, grind =]
theorem isType_llvmPointerType type : (llvmPointerType type).isType = true := by rfl
@[simp, grind =]
theorem isType_llvmArrayType type : (llvmArrayType type).isType = true := by rfl
@[simp, grind =]
theorem isType_llvmFunctionType type : (llvmFunctionType type).isType = true := by rfl
@[simp, grind =]
theorem isType_cudaTilePointerType type : (cudaTilePointerType type).isType = true := by rfl
@[simp, grind =]
theorem isType_hwModuleType type : (hwModuleType type).isType = true := by rfl
@[simp, grind =]
theorem isType_pdlAttributeType type : (pdlAttributeType type).isType = true := by rfl
@[simp, grind =]
theorem isType_pdlRangeType type : (pdlRangeType type).isType = true := by rfl
@[simp, grind =]
theorem isType_pdlOperationType type : (pdlOperationType type).isType = true := by rfl
@[simp, grind =]
theorem isType_pdlValueType type : (pdlValueType type).isType = true := by rfl
@[simp, grind =]
theorem isType_pdlTypeType type : (pdlTypeType type).isType = true := by rfl

end Attribute

/--
  An attribute that can be used as a type annotation for SSA values.
-/
@[expose]
def TypeAttr := {attr // Attribute.isType attr}
deriving Repr, Hashable, DecidableEq

instance : Inhabited TypeAttr where
  default := ⟨.integerType (IntegerType.mk 0), by rfl⟩

instance : Coe TypeAttr Attribute where
  coe typeAttr := typeAttr.val

instance : ToString TypeAttr where
  toString typeAttr := toString (typeAttr.val)

theorem TypeAttr.inj {attr1 attr2 : TypeAttr} :
  attr1 = attr2 ↔ (attr1 : Attribute) = (attr2 : Attribute) := by
  unfold TypeAttr at *
  grind

/--
  Convert an attribute to a type attribute.
-/
def Attribute.asType (attr : Attribute) (isType : attr.isType := by grind) : TypeAttr :=
  ⟨attr, isType⟩

/-- `Attribute.asType` is the identity on the underlying attribute. Stated so that `simp` and
`grind` can see through it without unfolding the semireducible `TypeAttr`. -/
@[simp, grind =]
theorem Attribute.asType_val {attr : Attribute} {isType : attr.isType} :
    (attr.asType isType).val = attr := by
  unfold Attribute.asType
  rfl

/--
`IsTypeAttr Attr` states that `Attr` is an attribute-specific type that can also
be converted to a `TypeAttr`.
-/
class IsTypeAttr (Attr : Type) extends IsAttr Attr, Coe Attr TypeAttr where
  /-- Converting to `TypeAttr` agrees with the injection into `Attribute`. -/
  coe_eq_inject (attr : Attr) : (coe attr).val = inject attr

namespace TypeAttr

/--
Try to cast a type attribute to a concrete attribute type.

This is equivalent to `mlir::dyn_cast<Attr>(attr)` in MLIR.
-/
@[inline]
def cast? (attr : TypeAttr) (Attr : Type) [IsTypeAttr Attr] : Option Attr :=
  attr.val.cast? Attr

/-- Try to cast a type attribute to a concrete attribute type, and throw an error if the cast
fails. -/
@[inline]
def cast! (attr : TypeAttr) (Attr : Type) [IsTypeAttr Attr] [Inhabited Attr] : Attr :=
  (cast? attr Attr).get!

/--
Check if a type attribute is of a specific type.

This is equivalent to `mlir::isa<Attr>(attr)` in MLIR.
-/
@[inline]
def isa (attr : TypeAttr) (Attr : Type) [IsTypeAttr Attr] : Bool :=
  match attr.cast? Attr with
  | some _ => true
  | none => false

/--
Cast a type attribute to a concrete attribute type, assuming it is of the expected type.

This is equivalent to `mlir::cast<Attr>(attr)` in MLIR.
-/
@[inline]
def cast (attr : TypeAttr) (Attr : Type) [IsTypeAttr Attr] [Inhabited Attr]
    (h : attr.isa Attr) : Attr :=
  (attr.cast? Attr).get (by grind [isa, cast?])

/-- Create a type attribute from a concrete attribute type. -/
@[inline]
def of (Attr : Type) [IsTypeAttr Attr] (specificAttr : Attr) : TypeAttr :=
  specificAttr

end TypeAttr

namespace IsTypeAttr

variable {Attr : Type} [IsTypeAttr Attr]

@[simp, grind =]
theorem cast?_of (specificAttr : Attr) :
    (TypeAttr.of Attr specificAttr).cast? Attr = some specificAttr := by
  simp [TypeAttr.of, TypeAttr.cast?, Attribute.of, IsTypeAttr.coe_eq_inject]

theorem of_injective : Function.Injective (TypeAttr.of Attr) := by
  intro attr₁ attr₂ h
  grind [congrArg (TypeAttr.cast? · Attr) h]

@[simp]
theorem cast?_eq_some_iff (attr : TypeAttr) (specificAttr : Attr) :
    attr.cast? Attr = some specificAttr ↔ TypeAttr.of Attr specificAttr = attr := by
  rw [TypeAttr.inj]
  simp [TypeAttr.cast?, TypeAttr.of, Attribute.of, IsTypeAttr.coe_eq_inject,
    IsAttr.cast?_eq_some_iff]

grind_pattern cast?_eq_some_iff =>
  attr.cast? Attr, TypeAttr.of Attr specificAttr

@[simp, grind =]
theorem isa_of (specificAttr : Attr) :
    (TypeAttr.of Attr specificAttr).isa Attr := by
  simp [TypeAttr.isa]

@[simp, grind =]
theorem cast!_of [Inhabited Attr] (specificAttr : Attr) :
    (TypeAttr.of Attr specificAttr).cast! Attr = specificAttr := by
  simp [TypeAttr.cast!]

@[simp, grind =]
theorem cast_of [Inhabited Attr] (specificAttr : Attr)
    (h : (TypeAttr.of Attr specificAttr).isa Attr) :
    (TypeAttr.of Attr specificAttr).cast Attr h = specificAttr := by
  simp [TypeAttr.cast]

@[simp, grind =]
theorem of_cast [Inhabited Attr] (attr : TypeAttr) (h : attr.isa Attr) :
    TypeAttr.of Attr (attr.cast Attr h) = attr := by
  rw [TypeAttr.inj]
  simp only [TypeAttr.of, IsTypeAttr.coe_eq_inject]
  exact IsAttr.of_cast attr.val h

end IsTypeAttr

/-!
  ## Coercion instances to TypeAttr

  We define a coercion from each attribute structure to `TypeAttr` if the attribute
  can be used as a type annotation.
-/

instance : IsTypeAttr IntegerType where
  coe type := Attribute.asType (.integerType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr FloatType where
  coe type := Attribute.asType (.floatType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr LLVM.ByteType where
  coe type := Attribute.asType (.byteType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr FunctionType where
  coe type := Attribute.asType (.functionType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr LLVMFunctionType where
  coe type := Attribute.asType (.llvmFunctionType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr ModArithType where
  coe type := Attribute.asType (.modArithType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : CoeDep (Option Nat → RegisterType) RegisterType.mk TypeAttr where
  coe := Attribute.asType (.registerType (.mk none)) (by rfl)

instance : IsTypeAttr RegisterType where
  coe type := Attribute.asType (.registerType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr LLVM.VoidType where
  coe type := Attribute.asType (.llvmVoidType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr LLVM.PointerType where
  coe type := Attribute.asType (.llvmPointerType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr LLVM.ArrayType where
  coe type := Attribute.asType (.llvmArrayType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr CudaTile.PointerType where
  coe type := Attribute.asType (.cudaTilePointerType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr HW.ModuleType where
  coe type := Attribute.asType (.hwModuleType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr PDL.RangeType where
  coe type := Attribute.asType (.pdlRangeType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr Match.OptionalType where
  coe type := Attribute.asType (.matchOptionalType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr PDL.AttributeType where
  coe type := Attribute.asType (.pdlAttributeType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr PDL.OperationType where
  coe type := Attribute.asType (.pdlOperationType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr PDL.ValueType where
  coe type := Attribute.asType (.pdlValueType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr PDL.TypeType where
  coe type := Attribute.asType (.pdlTypeType type) (by rfl)
  coe_eq_inject _ := by rfl

instance : IsTypeAttr TypeAttr where
  name := "TypeAttr"
  inject := fun x => x.val
  project := fun attr => if h: attr.isType then attr.asType else none
  coe := id
  coe_eq_inject := by simp
  project_eq_some_iff _ _ := by
    simp only [Option.dite_none_right_eq_some, Option.some.injEq, TypeAttr.inj]
    grind

end
end Veir
