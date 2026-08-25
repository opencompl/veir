module

public import Veir.PatternRewriter.Puddle.Definitions

/-! Resolution and binding of Puddle metadata tuples. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Abstract access to the metadata portion of a concrete or semantic assignment. -/
class MetadataStore (OpInfo : Type) [HasOpInfo OpInfo] (Store : Type) where
  getType : Store → Handle OpInfo .type → Option TypeAttr
  getProperty : (store : Store) → {opCode : OpInfo} →
    Handle OpInfo (.prop opCode) → Option (propertiesOf opCode)
  bindType : Store → Handle OpInfo .type → TypeAttr → Option Store
  bindProperty : (store : Store) → {opCode : OpInfo} →
    Handle OpInfo (.prop opCode) → propertiesOf opCode → Option Store

namespace MetadataTuple.Atom

/-- Resolve a metadata atom's handle against a metadata store. -/
@[expose]
def resolve {Handle Store : Type} [MetadataStore OpInfo Store] :
    (metadataAtom : MetadataTuple.Atom OpInfo Handle) → Store → Handle → Option metadataAtom.Value
| .type, store, handle => MetadataStore.getType store handle
| .property _, store, handle => MetadataStore.getProperty store handle

/-- Bind a metadata atom's handle to its corresponding value. -/
@[expose]
def bind {Handle Store : Type} [MetadataStore OpInfo Store] :
    (metadataAtom : MetadataTuple.Atom OpInfo Handle) → Store → Handle → metadataAtom.Value → Option Store
| .type, store, handle, value => MetadataStore.bindType store handle value
| .property _, store, handle, value => MetadataStore.bindProperty store handle value

end MetadataTuple.Atom

namespace MetadataTuple.Shape

/-- Resolve every handle in a metadata-tuple shape against a metadata store. -/
@[expose]
def resolve {Store : Type} [MetadataStore OpInfo Store] :
    (shape : MetadataTuple.Shape OpInfo Handles) → Store → Handles → Option shape.Values
| .unit, _, _ => some ()
| .atom metadataAtom, store, handle => metadataAtom.resolve store handle
| .cons head tail, store, handles => do
    let headValue ← head.resolve store handles.1
    let tailValues ← tail.resolve store handles.2
    return (headValue, tailValues)

/-- Bind every handle in a metadata-tuple shape to its corresponding value. -/
@[expose]
def bind {Store : Type} [MetadataStore OpInfo Store] :
    (shape : MetadataTuple.Shape OpInfo Handles) → Store → Handles → shape.Values → Option Store
| .unit, store, _, _ => some store
| .atom metadataAtom, store, handle, value => metadataAtom.bind store handle value
| .cons head tail, store, handles, values => do
    let store ← head.bind store handles.1 values.1
    tail.bind store handles.2 values.2

end MetadataTuple.Shape

namespace MetadataTuple

/-- Resolve all handles in a metadata tuple against a metadata store. -/
@[expose]
def resolve {Handles Store : Type} [self : IsMetadataTuple OpInfo Handles]
    [MetadataStore OpInfo Store]
    (store : Store) (handles : Handles) : Option (MetadataValues OpInfo Handles) :=
  self.shape.resolve store handles

/-- Bind all handles in a metadata tuple to their corresponding values. -/
@[expose]
def bind {Handles Store : Type} [self : IsMetadataTuple OpInfo Handles]
    [MetadataStore OpInfo Store]
    (store : Store) (handles : Handles) (values : MetadataValues OpInfo Handles) : Option Store :=
  self.shape.bind store handles values

/-! Canonical tuple equations used when reducing inline native declarations in validity proofs. -/

@[simp]
theorem resolve_unit {Store : Type} [MetadataStore OpInfo Store]
    (store : Store) (handles : Unit) :
    resolve (OpInfo := OpInfo) store handles = some () := by
  rfl

@[simp]
theorem resolve_type {Store : Type} [MetadataStore OpInfo Store]
    (store : Store) (handle : Handle OpInfo .type) :
    resolve (OpInfo := OpInfo) store handle = MetadataStore.getType store handle := by
  rfl

@[simp]
theorem resolve_property {Store : Type} [MetadataStore OpInfo Store]
    (store : Store) {opCode : OpInfo} (handle : Handle OpInfo (.prop opCode)) :
    resolve (OpInfo := OpInfo) store handle = MetadataStore.getProperty store handle := by
  rfl

@[simp]
theorem resolve_type_cons {Store Tail : Type} [MetadataStore OpInfo Store]
    [IsMetadataTuple OpInfo Tail]
    (store : Store) (handles : Handle OpInfo .type × Tail) :
    resolve (OpInfo := OpInfo) store handles = do
      let headValue ← MetadataStore.getType store handles.1
      let tailValues ← resolve (OpInfo := OpInfo) store handles.2
      return (headValue, tailValues) := by
  rfl

@[simp]
theorem resolve_property_cons {Store Tail : Type} [MetadataStore OpInfo Store]
    [IsMetadataTuple OpInfo Tail]
    (store : Store) {opCode : OpInfo} (handles : Handle OpInfo (.prop opCode) × Tail) :
    resolve (OpInfo := OpInfo) store handles = do
      let headValue ← MetadataStore.getProperty store handles.1
      let tailValues ← resolve (OpInfo := OpInfo) store handles.2
      return (headValue, tailValues) := by
  rfl

@[simp]
theorem bind_unit {Store : Type} [MetadataStore OpInfo Store]
    (store : Store) (handles values : Unit) :
    bind (OpInfo := OpInfo) store handles values = some store := by
  rfl

@[simp]
theorem bind_type {Store : Type} [MetadataStore OpInfo Store]
    (store : Store) (handle : Handle OpInfo .type) (value : TypeAttr) :
    bind (OpInfo := OpInfo) store handle value = MetadataStore.bindType store handle value := by
  rfl

@[simp]
theorem bind_property {Store : Type} [MetadataStore OpInfo Store]
    (store : Store) {opCode : OpInfo} (handle : Handle OpInfo (.prop opCode))
    (value : propertiesOf opCode) :
    bind (OpInfo := OpInfo) store handle value = MetadataStore.bindProperty store handle value := by
  rfl

end MetadataTuple

end

end Veir.Puddle
