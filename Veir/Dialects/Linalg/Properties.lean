module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `linalg.generic` operation.

  The operands are split into `numInputs` inputs followed by `numOutputs` outputs,
  with one indexing map per operand. MLIR spells this split as the
  `operandSegmentSizes` dense array `[numInputs, numOutputs]`, which is decoded when
  parsing and rebuilt when printing, so that rewrites and proofs work with plain
  numbers. The number of outputs is stored rather than derived from the operands, as
  printing does not see them, and the verifier checks both against the operands.
-/
structure LinalgGenericProperties where
  indexingMaps : Array AffineMapAttr
  iteratorTypes : Array Linalg.IteratorType
  numInputs : Nat
  numOutputs : Nat
  doc : Option StringAttr := none
  libraryCall : Option StringAttr := none
deriving Inhabited, Repr, Hashable, DecidableEq

/-- The property names `linalg.generic` accepts, as spelled in MLIR. -/
private def linalgGenericPropertyNames : List ByteArray :=
  ["indexing_maps", "iterator_types", "operandSegmentSizes", "doc", "library_call"].map
    (·.toUTF8)

/-- Read an optional string property of `linalg.generic`. -/
private def linalgGenericStringProperty (attrDict : Std.HashMap ByteArray Attribute)
    (field : String) : Except String (Option StringAttr) :=
  match attrDict[field.toUTF8]? with
  | none => pure none
  | some (.stringAttr attr) => pure (some attr)
  | some attr =>
    throw s!"linalg.generic: expected '{field}' to be a string attribute, but got {attr}"

def LinalgGenericProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LinalgGenericProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (key, _) =>
      !linalgGenericPropertyNames.contains key) then
    throw s!"linalg.generic: unexpected property '{String.fromUTF8! key}'"

  let some mapsAttr := attrDict["indexing_maps".toUTF8]?
    | throw "linalg.generic: requires attribute 'indexing_maps'"
  let .arrayAttr mapsAttr := mapsAttr
    | throw s!"linalg.generic: expected 'indexing_maps' to be an array attribute, but got {mapsAttr}"
  let indexingMaps ← mapsAttr.value.mapM fun
    | .affineMapAttr map => pure map
    | attr => throw s!"linalg.generic: expected 'indexing_maps' to contain affine maps, but got {attr}"

  let some iteratorsAttr := attrDict["iterator_types".toUTF8]?
    | throw "linalg.generic: requires attribute 'iterator_types'"
  let .arrayAttr iteratorsAttr := iteratorsAttr
    | throw s!"linalg.generic: expected 'iterator_types' to be an array attribute, but got {iteratorsAttr}"
  let iteratorTypes ← iteratorsAttr.value.mapM fun
    | .linalgIteratorTypeAttr iterator => pure iterator.value
    | attr => throw s!"linalg.generic: expected 'iterator_types' to contain iterator types, but got {attr}"

  -- Only the encoding of the segment sizes is checked here; the verifier checks them
  -- against the operands, as MLIR does.
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "linalg.generic: requires attribute 'operandSegmentSizes'"
  let .denseArrayAttr sizes := sizesAttr
    | throw s!"linalg.generic: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  if sizes.elementType ≠ .signless 32 then
    throw "linalg.generic: Expected 'operandSegmentSizes' to be an i32 dense array attribute"
  let #[numInputs, numOutputs] := sizes.values
    | throw s!"linalg.generic: operandSegmentSizes expected 2 entries, got {sizes.values.size}"
  if let some size := sizes.values.find? (· < 0) then
    throw s!"linalg.generic: operandSegmentSizes contains negative size {size}"

  let doc ← linalgGenericStringProperty attrDict "doc"
  let libraryCall ← linalgGenericStringProperty attrDict "library_call"

  return {
    indexingMaps, iteratorTypes, numInputs := numInputs.toNat,
    numOutputs := numOutputs.toNat, doc, libraryCall }

def LinalgGenericProperties.toAttrDict (props : LinalgGenericProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict : Std.HashMap ByteArray Attribute := Std.HashMap.emptyWithCapacity 5
  dict := dict.insert "indexing_maps".toUTF8
    (.arrayAttr ⟨props.indexingMaps.map .affineMapAttr⟩)
  dict := dict.insert "iterator_types".toUTF8
    (.arrayAttr ⟨props.iteratorTypes.map (.linalgIteratorTypeAttr ⟨·⟩)⟩)
  dict := dict.insert "operandSegmentSizes".toUTF8
    (.denseArrayAttr ⟨.signless 32, #[props.numInputs, props.numOutputs]⟩)
  if let some doc := props.doc then
    dict := dict.insert "doc".toUTF8 (.stringAttr doc)
  if let some libraryCall := props.libraryCall then
    dict := dict.insert "library_call".toUTF8 (.stringAttr libraryCall)
  return dict

/--
  The size of every loop of a `linalg.generic` and the operand it is taken from, given
  the static shapes of its operands in operand order, with `#[]` for a scalar operand.

  The size of a loop is the first operand dimension it indexes as a plain dimension
  `d<i>`, and it is `none` if no indexing map contains `d<i>`.
-/
def LinalgGenericProperties.loopSizes (props : LinalgGenericProperties)
    (operandShapes : Array (Array Nat)) : Array (Option (Nat × Nat)) := Id.run do
  let operands := props.indexingMaps.zip operandShapes
  let mut bounds : Array (Option (Nat × Nat)) := .replicate props.iteratorTypes.size none
  for h : k in [0:operands.size] do
    let (map, shape) := operands[k]
    for (result, size) in map.results.zip shape do
      if let .dim i := result then
        if bounds[i.val]? = some none then
          bounds := bounds.set! i.val (some (size, k))
  return bounds

/--
  The size of every loop of a `linalg.generic`, given the static shapes of its
  operands as for `loopSizes`, or `none` if some loop appears in no indexing map.

  The verifier rejects the latter, so a verified operation has loop bounds, and a
  rewrite and its proof can both use this function.
-/
def LinalgGenericProperties.loopBounds (props : LinalgGenericProperties)
    (operandShapes : Array (Array Nat)) : Option (List Nat) :=
  (props.loopSizes operandShapes).toList.mapM (·.map (·.1))

/--
  Verify the indexing maps of a `linalg.generic` against the static shapes of its
  operands, given in operand order, with `#[]` for a scalar operand.

  This mirrors MLIR's `IndexingMapOpInterface::verifyImpl`. Every loop must appear as
  a plain dimension `d<i>` in some indexing map, and its size is taken from the first
  operand dimension it indexes. Every other dimension indexed by `d<i>` must agree with
  that size, and a constant must lie within the dimension it indexes. As in MLIR,
  operand dimensions of size 0 are not checked.
-/
def LinalgGenericProperties.verifyIndexingMaps (props : LinalgGenericProperties)
    (operandShapes : Array (Array Nat)) : Except String Unit := do
  let numLoops := props.iteratorTypes.size
  if props.indexingMaps.size ≠ operandShapes.size then
    throw s!"expected the number of indexing maps ({props.indexingMaps.size}) to be equal \
      to the number of operands ({operandShapes.size})"
  let operands := props.indexingMaps.zip operandShapes
  for h : k in [0:operands.size] do
    let (map, shape) := operands[k]
    if map.numDims ≠ numLoops then
      throw s!"expected indexing map #{k} to have {numLoops} dim(s) to match the number of loops"
    if map.results.size ≠ shape.size then
      throw s!"expected operand #{k} rank ({shape.size}) to match the result rank of \
        indexing map #{k} ({map.results.size})"
  let bounds := props.loopSizes operandShapes
  for h : i in [0:bounds.size] do
    if bounds[i].isNone then
      throw s!"d{i} does not appear in any indexing map"
  for h : k in [0:operands.size] do
    let (map, shape) := operands[k]
    for (result, size) in map.results.zip shape do
      if size = 0 then
        continue
      match result with
      | .dim i =>
        let (loopSize, source) := bounds[i.val]!.get!
        if loopSize ≠ size then
          throw s!"d{i} has size {loopSize} from operand {source} but {size} from operand {k}"
      | .const c =>
        if c < 0 ∨ c ≥ size then
          throw s!"constant {c} in indexing map #{k} is out of bounds for a dimension of size {size}"

end

end Veir
