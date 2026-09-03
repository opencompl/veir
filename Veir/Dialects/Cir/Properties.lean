module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/-! ## Enumerations

ClangIR prints its enum attributes as plain `i32` integers in generic form, so each kind
carries its ClangIR numeric code.
-/

/-- The comparison kinds of `cir.cmp`, numbered as in ClangIR's `CmpOpKind`. -/
inductive CirCmpKind where
  | lt
  | le
  | gt
  | ge
  | eq
  | ne
deriving Inhabited, Repr, Hashable, DecidableEq

def CirCmpKind.ofNat? : Nat → Option CirCmpKind
  | 0 => some .lt
  | 1 => some .le
  | 2 => some .gt
  | 3 => some .ge
  | 4 => some .eq
  | 5 => some .ne
  | _ => none

def CirCmpKind.toNat : CirCmpKind → Nat
  | .lt => 0
  | .le => 1
  | .gt => 2
  | .ge => 3
  | .eq => 4
  | .ne => 5

/--
  The cast kinds of `cir.cast` that VeIR models, numbered as in ClangIR's `CastKind`.
  Every other kind is kept as `other` so that it round-trips; only the lowering rejects it.
-/
inductive CirCastKind where
  | integral
  | int_to_bool
  | bool_to_int
  | other (code : Nat)
deriving Inhabited, Repr, Hashable, DecidableEq

def CirCastKind.ofNat : Nat → CirCastKind
  | 27 => .integral
  | 28 => .int_to_bool
  | 38 => .bool_to_int
  | code => .other code

def CirCastKind.toNat : CirCastKind → Nat
  | .integral => 27
  | .int_to_bool => 28
  | .bool_to_int => 38
  | .other code => code

/-- The value of a `cir.const`: a typed integer or boolean constant. -/
inductive CirConstValue where
  | int (attr : CirIntAttr)
  | bool (attr : CirBoolAttr)
deriving Inhabited, Repr, Hashable, DecidableEq

def CirConstValue.toAttribute : CirConstValue → Attribute
  | .int attr => .cirIntAttr attr
  | .bool attr => .cirBoolAttr attr

/-- The type a constant value carries, which its result must match. -/
def CirConstValue.type : CirConstValue → Attribute
  | .int attr => .cirIntType attr.type
  | .bool _ => .cirBoolType {}

/-! ## Helpers -/

/-- Reject properties on operations whose schema carries none. -/
def Cir.noProperties (attrDict : Std.HashMap ByteArray Attribute) : Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    .error s!"cir: expected no properties, but got {attrDict.size} {plural}"
  else
    .ok ()

/-- Read a `kind = N : i32` enum property. -/
private def getKind (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Nat := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only 'kind' property, but got {attrDict.size} properties"
  let some attr := attrDict["kind".toUTF8]?
    | throw s!"{opName}: missing 'kind' property"
  let .integerAttr intAttr := attr
    | throw s!"{opName}: expected 'kind' to be an integer attribute, but got {attr}"
  if intAttr.type.bitwidth ≠ 32 then
    throw s!"{opName}: expected 'kind' to be an i32 attribute, but got {attr}"
  if intAttr.value < 0 then
    throw s!"{opName}: invalid kind {intAttr.value}"
  return intAttr.value.toNat

private def kindAttr (kind : Nat) : Attribute :=
  .integerAttr (IntegerAttr.mk (Int.ofNat kind) (IntegerType.mk 32))

/-! ## Properties -/

/--
  Properties of `cir.func`. Its `sym_name` and `function_type` are modelled explicitly;
  every other attribute (linkage, visibility, calling convention, ...) is preserved
  verbatim in `extra`.
-/
structure CirFuncProperties where
  sym_name : StringAttr
  function_type : CirFuncType
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CirFuncProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CirFuncProperties := do
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr s) => pure s
    | some attr => throw s!"cir.func: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "cir.func: missing 'sym_name' property"
  let funcType ← match attrDict["function_type".toUTF8]? with
    | some (.cirFuncType ft) => pure ft
    | some attr =>
      throw s!"cir.func: expected 'function_type' to be a !cir.func type, but got {attr}"
    | none => throw "cir.func: missing 'function_type' property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 && k ≠ "function_type".toUTF8)
  return { sym_name := symName, function_type := funcType, extra }

/-- Properties of `cir.const`. -/
structure CirConstProperties where
  value : CirConstValue
deriving Inhabited, Repr, Hashable, DecidableEq

def CirConstProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CirConstProperties := do
  if attrDict.size > 1 then
    throw s!"cir.const: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "cir.const: missing 'value' property"
  match attr with
  | .cirIntAttr intAttr => return { value := .int intAttr }
  | .cirBoolAttr boolAttr => return { value := .bool boolAttr }
  | attr => throw s!"cir.const: expected 'value' to be a #cir.int or #cir.bool attribute, but got {attr}"

/--
  Properties of `cir.add`, `cir.sub` and `cir.minus`. ClangIR always prints their
  `no_signed_wrap`, `no_unsigned_wrap` and `saturated` flags; they are kept verbatim so that
  the operation round-trips, and read with `flagSet`.
-/
structure CirOverflowFlagsProperties where
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CirOverflowFlagsProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CirOverflowFlagsProperties :=
  return { extra := DictionaryAttr.fromArray attrDict.toArray }

/-- Whether a flag is set: present as a unit attribute, or as a non-zero `i1`. -/
def CirOverflowFlagsProperties.flagSet (props : CirOverflowFlagsProperties) (key : String) :
    Bool :=
  match props.extra.entries.find? (fun (k, _) => k = key.toUTF8) with
  | some (_, .unitAttr _) => true
  | some (_, .integerAttr attr) => attr.value ≠ 0
  | _ => false

/-- Properties of `cir.shift`: `isShiftleft` is a unit attribute, absent for right shifts. -/
structure CirShiftProperties where
  isShiftleft : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def CirShiftProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CirShiftProperties := do
  if attrDict.size > 1 then
    throw s!"cir.shift: expected only 'isShiftleft' property, but got {attrDict.size} properties"
  match attrDict["isShiftleft".toUTF8]? with
  | none => return { isShiftleft := false }
  | some (.unitAttr _) => return { isShiftleft := true }
  | some attr => throw s!"cir.shift: expected 'isShiftleft' to be a unit attribute, but got {attr}"

/-- Properties of `cir.cmp`. -/
structure CirCmpProperties where
  kind : CirCmpKind
deriving Inhabited, Repr, Hashable, DecidableEq

def CirCmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CirCmpProperties := do
  let code ← getKind "cir.cmp" attrDict
  let some kind := CirCmpKind.ofNat? code
    | throw s!"cir.cmp: invalid kind {code}"
  return { kind }

/-- Properties of `cir.cast`. -/
structure CirCastProperties where
  kind : CirCastKind
deriving Inhabited, Repr, Hashable, DecidableEq

def CirCastProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CirCastProperties := do
  let code ← getKind "cir.cast" attrDict
  return { kind := CirCastKind.ofNat code }

/-- Properties of `cir.brcond`. -/
structure CirBrCondProperties where
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CirBrCondProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CirBrCondProperties := do
  if attrDict.size > 1 then
    throw s!"cir.brcond: expected only 'operandSegmentSizes' property, but got {attrDict.size} properties"
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "cir.brcond: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"cir.brcond: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  return { operandSegmentSizes := sizesAttr }

/-! ## Attribute dictionaries -/

def CirFuncProperties.toAttrDict (props : CirFuncProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    dict := dict.insert "function_type".toUTF8 (.cirFuncType props.function_type)
    dict

def CirConstProperties.toAttrDict (props : CirConstProperties) : Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 props.value.toAttribute

def CirOverflowFlagsProperties.toAttrDict (props : CirOverflowFlagsProperties) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.ofList props.extra.entries.toList

def CirShiftProperties.toAttrDict (props : CirShiftProperties) : Std.HashMap ByteArray Attribute :=
  if props.isShiftleft then
    (Std.HashMap.emptyWithCapacity 1).insert "isShiftleft".toUTF8 (.unitAttr UnitAttr.mk)
  else
    Std.HashMap.emptyWithCapacity 0

def CirCmpProperties.toAttrDict (props : CirCmpProperties) : Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "kind".toUTF8 (kindAttr props.kind.toNat)

def CirCastProperties.toAttrDict (props : CirCastProperties) : Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "kind".toUTF8 (kindAttr props.kind.toNat)

def CirBrCondProperties.toAttrDict (props : CirBrCondProperties) :
    Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "operandSegmentSizes".toUTF8
    (.denseArrayAttr props.operandSegmentSizes)

end

end Veir
