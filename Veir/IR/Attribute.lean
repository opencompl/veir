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
  separate functions for each case.
-/

namespace Veir
public section

/--
  A data structure that represents compile-time information in the IR.
  Attributes are used either as type annotations for SSA values, or
  as extra information stored in operations.
-/
inductive Attribute
| integerType (bitwidth : Nat)
/--
  An attribute from an unknown dialect.
-/
| unregistered (value : String) (isType : Bool)
deriving Inhabited, Repr, DecidableEq, Hashable

namespace Attribute

/--
  Determine if an attribute can be used as a type annotation for SSA
  values.
-/
def isType (attr : Attribute) : Bool :=
  match attr with
  | .integerType _ => true
  | .unregistered _ isType => isType

@[simp, grind =]
theorem isType_integerType bitwidth : (integerType bitwidth).isType = true := by rfl
@[simp, grind =]
theorem isType_unregistered value isType : (unregistered value isType).isType = isType := by rfl

/--
  Convert an attribute to a string representation.
-/
def toString (attr : Attribute) : String :=
  match attr with
  | .integerType bitwidth => s!"i{bitwidth}"
  | .unregistered value _ => value

instance : ToString Attribute where
  toString := toString

end Attribute

/--
  An attribute that can be used as a type annotation for SSA values.
-/
@[expose]
def TypeAttr := {attr // Attribute.isType attr}
deriving Repr, Hashable, DecidableEq

instance : Inhabited TypeAttr where
  default := ⟨.integerType 0, by rfl⟩

instance : Coe TypeAttr Attribute where
  coe typeAttr := typeAttr.val

instance : ToString TypeAttr where
  toString typeAttr := toString (typeAttr.val)

/--
  Convert an attribute to a type attribute.
-/
def Attribute.asType (attr : Attribute) (isType : attr.isType := by grind) : TypeAttr :=
  ⟨attr, isType⟩

end
end Veir
