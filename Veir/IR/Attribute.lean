module

public import Veir.ForLean

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

/-! ## Attribute definitions -/

/--
  A `!builtin.integer` is an integer type with a given bitwidth.
-/
structure IntegerType where
  bitwidth : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  An attribute from an unknown dialect.
  It can be either a type attribute or a non-type attribute.
-/
structure UnregisteredAttr where
  value : String
  isType : Bool
deriving Inhabited, Repr, DecidableEq, Hashable

mutual

structure FunctionType where
  inputs : Array Attribute
  outputs : Array Attribute
deriving Inhabited, Repr, Hashable

/--
  A data structure that represents compile-time information in the IR.
  Attributes are used either as type annotations for SSA values, or
  as extra information stored in operations.
-/
inductive Attribute
/-- Integer type -/
| integerType (type : IntegerType)
/-- Function type -/
| functionType (type : FunctionType)
/-- An attribute from an unknown dialect. -/
| unregisteredAttr (attr : UnregisteredAttr)
deriving Inhabited, Repr, Hashable

end

theorem FunctionType.sizeOf_elems (ft : FunctionType) : 
    (∀ x, x ∈ ft.inputs → sizeOf x < sizeOf ft) ∧ (∀ x, x ∈ ft.outputs → sizeOf x < sizeOf ft) := by 
  apply @FunctionType.recOn 
    (fun ft => 
      (∀ x, x ∈ ft.inputs → sizeOf x < sizeOf ft) ∧ (∀ x, x ∈ ft.outputs → sizeOf x < sizeOf ft)) 
    (fun x => True)
    (fun as => ∀ x, x ∈ as → sizeOf x < sizeOf as)
    (fun as => ∀ x, x ∈ as → sizeOf x < sizeOf as)
    ft
  all_goals grind

theorem FunctionType.sizeOf_elems_inputs (ft : FunctionType) (hx : x ∈ ft.inputs) : 
    sizeOf x < sizeOf ft :=
  (sizeOf_elems ft).1 _ hx

theorem FunctionType.sizeOf_elems_outputs (ft : FunctionType) (hx : x ∈ ft.outputs) : 
    sizeOf x < sizeOf ft :=
  (sizeOf_elems ft).2 _ hx

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
      isTrue (by grind [cases FunctionType])
    | isFalse _ =>
      isFalse (by grind)
  | isFalse _ =>
    isFalse (by grind)
termination_by sizeOf type1
decreasing_by
  · have := @FunctionType.sizeOf_elems_inputs
    grind
  · have := @FunctionType.sizeOf_elems_outputs
    grind

def Attribute.decEq (attr1 attr2 : Attribute) : Decidable (attr1 = attr2) :=
  match h1 : attr1, h2 : attr2 with
  | .integerType type1, .integerType type2 =>
    match decEq type1 type2 with
    | isTrue hEq => isTrue (by grind)
    | isFalse hEq => isFalse (by grind)
  | .unregisteredAttr attr1, .unregisteredAttr attr2 =>
    match decEq attr1 attr2 with
    | isTrue hEq => isTrue (by grind)
    | isFalse hEq => isFalse (by grind)
  | .functionType type1, .functionType type2 =>
    match FunctionType.decEq type1 type2 with
    | isTrue hEq => isTrue (by grind)
    | isFalse hEq => isFalse (by grind)
  | .integerType _, .unregisteredAttr _
  | .integerType _, .functionType _
  | .functionType _, .integerType _ 
  | .functionType _, .unregisteredAttr _
  | .unregisteredAttr _, .integerType _ 
  | .unregisteredAttr _, .functionType _ =>
     isFalse (by grind)
termination_by sizeOf attr1
end

instance : DecidableEq Attribute := Attribute.decEq
instance : DecidableEq FunctionType := FunctionType.decEq

/-!
  ## ToString implementation

  `ToString` is used to convert attributes to their MLIR textual representation.
  It is also the syntax used for printing attributes in the REPL and in error messages.
-/

instance : ToString IntegerType where
  toString type := s!"i{type.bitwidth}"

instance : ToString UnregisteredAttr where
  toString attr := attr.value

mutual

def FunctionType.toString (type : FunctionType) : String :=
  let inputs := String.intercalate ", " (type.inputs.toList.map Attribute.toString)
  let outputs := String.intercalate ", " (type.outputs.toList.map Attribute.toString)
  s!"({inputs}) -> ({outputs})"
termination_by sizeOf type
decreasing_by
  · rename_i subAttr subAttrIn
    have : sizeOf type.inputs < sizeOf type := by
      grind [FunctionType.mk.sizeOf_spec, cases FunctionType]
    simp only [←Array.mem_def] at subAttrIn
    grind [Array.sizeOf_lt_of_mem subAttrIn]
  · rename_i subAttr subAttrIn
    have : sizeOf type.outputs < sizeOf type := by
      grind [FunctionType.mk.sizeOf_spec, cases FunctionType]
    simp only [←Array.mem_def] at subAttrIn
    grind [Array.sizeOf_lt_of_mem subAttrIn]

/--
  Convert an attribute to a string representation.
-/
def Attribute.toString (attr : Attribute) : String :=
  match attr with
  | .integerType type => ToString.toString type
  | .unregisteredAttr attr => ToString.toString attr
  | .functionType type => type.toString
termination_by sizeOf attr

end

instance : ToString Attribute where
  toString := Attribute.toString

instance : ToString FunctionType where
  toString := FunctionType.toString

/-!
  ## Coercion instances to Attribute

  We define a coercion from each attribute structure to `Attribute`.
-/
instance : Coe IntegerType Attribute where
  coe type := .integerType type

instance : Coe UnregisteredAttr Attribute where
  coe attr := .unregisteredAttr attr

instance : Coe FunctionType Attribute where
  coe type := .functionType type

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
  | .unregisteredAttr attr => attr.isType
  | .functionType _ => true

@[simp, grind =]
theorem isType_integerType type : (integerType type).isType = true := by rfl
@[simp, grind =]
theorem isType_unregistered unregistered :
  (unregisteredAttr unregistered).isType = unregistered.isType := by rfl
@[simp, grind =]
theorem isType_functionType type : (functionType type).isType = true := by rfl

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

/--
  Convert an attribute to a type attribute.
-/
def Attribute.asType (attr : Attribute) (isType : attr.isType := by grind) : TypeAttr :=
  ⟨attr, isType⟩

/-!
  ## Coercion instances to TypeAttr

  We define a coercion from each attribute structure to `TypeAttr` if the attribute
  can be used as a type annotation.
-/

instance : Coe IntegerType TypeAttr where
  coe type := ⟨.integerType type, by rfl⟩

instance : Coe FunctionType TypeAttr where
  coe type := ⟨.functionType type, by rfl⟩

end
end Veir
