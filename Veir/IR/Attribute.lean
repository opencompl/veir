module

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

/--
  A data structure that represents compile-time information in the IR.
  Attributes are used either as type annotations for SSA values, or
  as extra information stored in operations.
-/
inductive Attribute
| integerType (type : IntegerType)
/-- An attribute from an unknown dialect. -/
| unregisteredAttr (attr : UnregisteredAttr)
deriving Inhabited, Repr, DecidableEq, Hashable

/-!
  ## ToString implementation

  `ToString` is used to convert attributes to their MLIR textual representation.
  It is also the syntax used for printing attributes in the REPL and in error messages.
-/

instance : ToString IntegerType where
  toString type := s!"i{type.bitwidth}"

instance : ToString UnregisteredAttr where
  toString attr := attr.value

namespace Attribute

/--
  Convert an attribute to a string representation.
-/
def toString (attr : Attribute) : String :=
  match attr with
  | .integerType type => ToString.toString type
  | .unregisteredAttr attr => ToString.toString attr

instance : ToString Attribute where
  toString := toString

/-!
  ## Coercion instances to Attribute

  We define a coercion from each attribute structure to `Attribute`.
-/
instance : Coe IntegerType Attribute where
  coe type := .integerType type

instance : Coe UnregisteredAttr Attribute where
  coe attr := .unregisteredAttr attr

end Attribute

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

@[simp, grind =]
theorem isType_integerType type : (integerType type).isType = true := by rfl
@[simp, grind =]
theorem isType_unregistered unregistered :
  (unregisteredAttr unregistered).isType = unregistered.isType := by rfl

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

end
end Veir
