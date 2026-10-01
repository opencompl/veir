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

/-- Static layout for one ordered list of named operand or result groups. -/
structure NamedValueGroups where
  /-- Groups in the same order as their flattened runtime values. -/
  groups : Array NamedValueGroup := #[]
  /--
  Property key that stores one segment size per group. Required when more than
  one group has dynamic cardinality. If absent, a single dynamic group can be
  resolved from the total value count.
  -/
  segmentSizesProperty? : Option String := none
  deriving Inhabited, Repr, DecidableEq

namespace NamedValueGroups

/-- Find a group by syntax name and return its declaration index. -/
def findIndex? (groups : NamedValueGroups) (name : String) : Option Nat := Id.run do
  for index in [:groups.groups.size] do
    if groups.groups[index]!.name == name then
      return some index
  return none

/--
Resolve flattened values into group sizes. Pass stored segment sizes when the
operation uses a segment-size property or when the format has already parsed
explicit groups. The result is checked against every group's cardinality and
the total flattened value count.
-/
def resolveSizes (groups : NamedValueGroups) (total : Nat)
    (providedSizes? : Option (Array Nat) := none) : Except String (Array Nat) := do
  let sizes ← match providedSizes? with
    | some sizes =>
      if sizes.size != groups.groups.size then
        throw s!"expected {groups.groups.size} segment sizes, got {sizes.size}"
      pure sizes
    | none =>
      if groups.segmentSizesProperty?.isSome then
        throw s!"missing segment sizes property '{groups.segmentSizesProperty?.get!}'"
      let dynamicIndices := groups.groups.toList.zipIdx.filterMap fun (group, index) =>
        if group.cardinality.isDynamic then some index else none
      if dynamicIndices.isEmpty then
        pure (Array.replicate groups.groups.size 1)
      else if dynamicIndices.length == 1 then
        let dynamicIndex := dynamicIndices.head!
        let fixedCount := groups.groups.size - 1
        if total < fixedCount then
          throw s!"expected at least {fixedCount} values, got {total}"
        pure <| groups.groups.mapIdx fun index group =>
          if index == dynamicIndex then total - fixedCount
          else if group.cardinality == .one then 1
          else 0
      else
        throw "segment sizes are required when multiple operand or result groups are dynamic"
  let mut totalFromSegments := 0
  for (group, size) in groups.groups.zip sizes do
    if !group.cardinality.accepts size then
      throw s!"group '{group.name}' does not accept segment size {size}"
    totalFromSegments := totalFromSegments + size
  if totalFromSegments != total then
    throw s!"segment sizes describe {totalFromSegments} values, got {total}"
  pure sizes

end NamedValueGroups

/-- Whether a named operation field can be absent. -/
inductive OperationFieldPresence where
  | required
  | optional
  deriving Inhabited, Repr, DecidableEq

/-- A named attribute or property mapped to its canonical storage key. -/
structure NamedOperationField where
  /-- Name referenced by operation syntax, without a `$` prefix. -/
  name : String
  /-- Key used in the operation attribute dictionary or property dictionary. -/
  storageKey : String
  /-- Whether the field can be absent from an operation. -/
  presence : OperationFieldPresence := .required
  deriving Inhabited, Repr, DecidableEq

/-- Static, syntax-facing description of one operation. -/
structure OperationDefinition where
  operands : NamedValueGroups := {}
  results : NamedValueGroups := {}
  /-- Bindings stored in `Operation.attrs`. -/
  attributes : Array NamedOperationField := #[]
  /-- Bindings stored in opcode-specific properties. -/
  properties : Array NamedOperationField := #[]
  deriving Inhabited, Repr, DecidableEq

namespace OperationDefinition

private def isAsciiLetter (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') || ('A' ≤ character && character ≤ 'Z')

private def isIdentifierStart (character : Char) : Bool :=
  isAsciiLetter character || character == '_'

private def isIdentifierContinue (character : Char) : Bool :=
  isIdentifierStart character || ('0' ≤ character && character ≤ '9') ||
    character == '.' || character == '$'

private def isIdentifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => isIdentifierStart first && rest.all isIdentifierContinue

private def dynamicGroupCount (groups : NamedValueGroups) : Nat :=
  groups.groups.foldl (init := 0) fun count group =>
    count + if group.cardinality.isDynamic then 1 else 0

private def validateNames (names : Array String) : Except String Unit := do
  let mut seen : Array String := #[]
  for name in names do
    if !isIdentifier name then
      throw s!"invalid operation syntax name '{name}'"
    if seen.contains name then
      throw s!"duplicate operation syntax name '{name}'"
    seen := seen.push name

private def validateStorageKeys (kind : String) (fields : Array NamedOperationField) :
    Except String Unit := do
  let mut seen : Array String := #[]
  for field in fields do
    if field.storageKey.isEmpty then
      throw s!"empty {kind} storage key for operation syntax name '{field.name}'"
    if seen.contains field.storageKey then
      throw s!"duplicate {kind} storage key '{field.storageKey}'"
    seen := seen.push field.storageKey

private def validateGroups (label : String) (groups : NamedValueGroups) :
    Except String Unit := do
  if let some key := groups.segmentSizesProperty? then
    if key.isEmpty then
      throw s!"empty segment sizes property key for {label} groups"
  if dynamicGroupCount groups > 1 && groups.segmentSizesProperty?.isNone then
    throw s!"{label} groups with multiple dynamic groups require a segment sizes property"

/--
Validate syntax names, storage keys, and whether dynamic groups have enough
layout metadata to be resolved unambiguously.
-/
def validate (definition : OperationDefinition) : Except String Unit := do
  let mut names : Array String := #[]
  for group in definition.operands.groups do
    names := names.push group.name
  for group in definition.results.groups do
    names := names.push group.name
  for field in definition.attributes do
    names := names.push field.name
  for field in definition.properties do
    names := names.push field.name
  validateNames names
  validateStorageKeys "attribute" definition.attributes
  validateStorageKeys "property" definition.properties
  validateGroups "operand" definition.operands
  validateGroups "result" definition.results

/-- Find a named operand group and return its declaration index. -/
def findOperand? (definition : OperationDefinition) (name : String) : Option Nat :=
  definition.operands.findIndex? name

/-- Find a named result group and return its declaration index. -/
def findResult? (definition : OperationDefinition) (name : String) : Option Nat :=
  definition.results.findIndex? name

/-- Find a named attribute binding. -/
def findAttribute? (definition : OperationDefinition) (name : String) : Option NamedOperationField :=
  definition.attributes.find? (·.name == name)

/-- Find a named property binding. -/
def findProperty? (definition : OperationDefinition) (name : String) : Option NamedOperationField :=
  definition.properties.find? (·.name == name)

end OperationDefinition

end -- public section

end Veir
