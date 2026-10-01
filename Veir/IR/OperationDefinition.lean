module

namespace Veir

public section

/-- The number of values represented by one named operation group. -/
inductive ValueGroupCardinality where
  | one
  | optional
  | variadic
  deriving Inhabited, Repr, DecidableEq

namespace ValueGroupCardinality

/-- Whether a concrete group size is valid for this cardinality. -/
def accepts (cardinality : ValueGroupCardinality) (size : Nat) : Bool :=
  match cardinality with
  | .one => size == 1
  | .optional => size ≤ 1
  | .variadic => true

/-- Whether this cardinality can represent more than one possible size. -/
def isDynamic (cardinality : ValueGroupCardinality) : Bool :=
  cardinality != .one

end ValueGroupCardinality

/-- A named group of operation operands or results. -/
structure NamedValueGroup where
  /-- Name referenced by operation syntax, without a `$` prefix. -/
  name : String
  /-- Number of values represented by this group. -/
  cardinality : ValueGroupCardinality := .one
  deriving Inhabited, Repr, DecidableEq

/--
Find a group by syntax name and return its declaration index. Groups are
listed in the same order as their flattened runtime values.
-/
def findGroupIndex? (groups : Array NamedValueGroup) (name : String) : Option Nat :=
  Id.run do
    for index in [:groups.size] do
      if groups[index]!.name == name then
        return some index
    return none

/--
Resolve flattened values into group sizes. Pass the stored segment sizes when
`usesSegmentSizes` holds, or the sizes a format has already parsed per group.
Otherwise the sizes are inferred from the total value count. The result is
checked against every group's cardinality and the total flattened value count.
-/
def resolveSizes (groups : Array NamedValueGroup) (total : Nat)
    (providedSizes? : Option (Array Nat) := none) : Except String (Array Nat) := do
  let sizes ← match providedSizes? with
    | some sizes =>
      if sizes.size != groups.size then
        throw s!"expected {groups.size} segment sizes, got {sizes.size}"
      pure sizes
    | none =>
      let dynamicIndices := groups.toList.zipIdx.filterMap fun (group, index) =>
        if group.cardinality.isDynamic then some index else none
      if dynamicIndices.isEmpty then
        pure (Array.replicate groups.size 1)
      else if dynamicIndices.length == 1 then
        let dynamicIndex := dynamicIndices.head!
        let fixedCount := groups.size - 1
        if total < fixedCount then
          throw s!"expected at least {fixedCount} values, got {total}"
        pure <| groups.mapIdx fun index group =>
          if index == dynamicIndex then total - fixedCount
          else if group.cardinality == .one then 1
          else 0
      else
        throw "segment sizes are required when multiple operand or result groups are dynamic"
  let mut totalFromSegments := 0
  for (group, size) in groups.zip sizes do
    if !group.cardinality.accepts size then
      throw s!"group '{group.name}' does not accept segment size {size}"
    totalFromSegments := totalFromSegments + size
  if totalFromSegments != total then
    throw s!"segment sizes describe {totalFromSegments} values, got {total}"
  pure sizes

/-- Number of groups whose size is not statically fixed. -/
private def dynamicGroupCount (groups : Array NamedValueGroup) : Nat :=
  groups.foldl (init := 0) fun count group =>
    count + if group.cardinality.isDynamic then 1 else 0

/--
Whether this list of groups forces the operation to carry a segment sizes
property. MLIR requires `AttrSizedOperandSegments` / `AttrSizedResultSegments`
exactly when an operation has more than one variable-length group, so the
property is needed precisely when at least two groups are dynamic. The
property keys are fixed (`operandSegmentSizes` / `resultSegmentSizes`) and
carry no per-operation configuration.
-/
def usesSegmentSizes (groups : Array NamedValueGroup) : Bool :=
  dynamicGroupCount groups > 1

/--
Whether a named operation field can be absent. Mirrors MLIR's `OptionalAttr`.
Default-valued fields (`DefaultValuedAttr`) are not modelled yet; a
`defaultValued` case should be added when a format printer must omit defaults.
-/
inductive OperationFieldPresence where
  | required
  | optional
  deriving Inhabited, Repr, DecidableEq

/--
A named ODS attribute or property mapped to its opcode-specific property key.
Both ODS attributes and ODS properties live in `propertiesOf` in VeIR, while
discardable attr-dict entries are un-declared and are not described here.
-/
structure NamedOperationField where
  /-- Name referenced by operation syntax, without a `$` prefix. -/
  name : String
  /--
  Key used in the opcode-specific property dictionary. In ODS the name is the
  storage key, so this field is normally equal to `name`; it exists so a syntax
  name may differ from its storage key.
  -/
  storageKey : String
  /-- Whether the field can be absent from an operation. -/
  presence : OperationFieldPresence := .required
  deriving Inhabited, Repr, DecidableEq

/-- Static, syntax-facing description of one operation. -/
structure OperationDefinition where
  /--
  Operand groups in the same order as the operation's flattened operands.
  When the list has more than one dynamic group, the operation follows MLIR's
  `AttrSizedOperandSegments` convention (see `usesSegmentSizes`).
  -/
  operands : Array NamedValueGroup := #[]
  /-- Result groups in the same order as the operation's flattened results. -/
  results : Array NamedValueGroup := #[]
  /--
  Bindings for ODS-declared attributes and properties. In VeIR both are stored
  in the opcode-specific `propertiesOf` struct, so `$overflowFlags`, `$value`,
  and `$callee` are looked up here, not in the discardable attr-dict.
  -/
  properties : Array NamedOperationField := #[]
  deriving Inhabited, Repr, DecidableEq

namespace OperationDefinition

/-- Find a named operand group and return its declaration index. -/
def findOperand? (definition : OperationDefinition) (name : String) : Option Nat :=
  findGroupIndex? definition.operands name

/-- Find a named result group and return its declaration index. -/
def findResult? (definition : OperationDefinition) (name : String) : Option Nat :=
  findGroupIndex? definition.results name

/-- Find a named property binding. -/
def findProperty? (definition : OperationDefinition) (name : String) : Option NamedOperationField :=
  definition.properties.find? (·.name == name)

end OperationDefinition

end -- public section

end Veir
