module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

class HasDialectOpInfo (opCode: Type)
    extends Hashable opCode, Repr opCode, Inhabited opCode where
  /-- Look up an operation by its fully qualified MLIR name. -/
  fromName : ByteArray → Option opCode
  /-- Return an operation's fully qualified MLIR name. -/
  name : opCode → ByteArray
  propertiesOf : opCode → Type
  /-- Create an operation's properties from its attribute dictionary. -/
  fromAttrDict : (op : opCode) → Std.HashMap ByteArray Attribute →
    Except String (propertiesOf op)
  /-- Convert an operation's properties into an attribute dictionary. -/
  toAttrDict : (op : opCode) → propertiesOf op → Std.HashMap ByteArray Attribute
  propertiesHash {op : opCode} : Hashable (propertiesOf op) := by
    simp only [properties_of]
    intros opCode; cases opCode <;>
    ((try rename_i op; cases op) <;> infer_instance)
  propertiesDefault {op : opCode} : Inhabited (propertiesOf op) := by
    simp only [properties_of]
    intros opCode; cases opCode <;>
    ((try rename_i op; cases op) <;> infer_instance)
  propertiesRepr {op : opCode} : Repr (propertiesOf op) := by
    simp only [properties_of]
    intros opCode; cases opCode <;>
    ((try rename_i op; cases op) <;> infer_instance)
  propertiesDecideEq {op : opCode} : DecidableEq (propertiesOf op) := by
    simp only [properties_of]
    intros opCode; cases opCode <;>
    ((try rename_i op; cases op) <;> infer_instance)
  decideEq : DecidableEq (opCode) := by
    intros opCode1 opCode2; cases opCode1 <;> cases opCode2 <;> infer_instance
  /--
  Whether an operation with this opcode and these properties may have
  effects that make it ineligible for transformations that add /
  remove / rearrange instructions (terminators count as having
  effects). Defaults to `true` for every opcode, which conservatively
  disables such transformations.
  -/
  hasSideEffects : (op : opCode) → propertiesOf op → Bool := fun _ _ => true
  /--
  Whether an operation with this opcode reads memory.

  This is deliberately separate from `hasSideEffects`: a non-volatile load
  reads memory and yet is eligible for removal when its result is unused, so
  `hasSideEffects` reports `false` for it. Fold-time evaluation must consult
  this as well before running an operation against memory that is not the
  program's.

  Defaults to `true` for every opcode, which conservatively assumes memory is
  read.
  -/
  readsMemory : opCode → Bool := fun _ => true
  /--
  Whether an operation with this opcode materializes a literal constant
  value: no operands, one result, no side effects, and a result that is
  always determined by the operation's properties. Defaults to `false`
  for every opcode, which conservatively treats nothing as constant.
  -/
  isConstantLike : opCode → Bool := fun _ => false
  /--
  Whether definitions in the indexed region must dominate their uses. A false
  result denotes graph-style semantics, where only a single block can be in the
  region, and operation order does not impose SSA dominance.
  -/
  hasSSADominance : opCode → Nat → Bool
  /--
  Whether the indexed region is exempt from the requirement that each of its
  blocks ends in a terminator, mirroring MLIR's `NoTerminator` trait.

  This is deliberately separate from the region kind. A graph region implies
  no terminator, but the converse does not hold: MLIR gives `pdl.rewrite` a
  body that is an ordinary SSACFG region and yet carries `NoTerminator`.
  Encoding such a region as a graph region would silently drop SSA dominance
  from the model in order to relax an unrelated requirement.

  Defaults to `false` for every opcode, which conservatively keeps the
  terminator requirement.
  -/
  hasNoTerminator : opCode → Nat → Bool := fun _ _ => false

instance [HasDialectOpInfo opCode] {op : opCode} : Hashable (HasDialectOpInfo.propertiesOf op) where
  hash := HasDialectOpInfo.propertiesHash.hash

instance [HasDialectOpInfo opCode] {op : opCode} : Inhabited (HasDialectOpInfo.propertiesOf op) where
  default := HasDialectOpInfo.propertiesDefault.default

instance [HasDialectOpInfo opCode] {op : opCode} : Repr (HasDialectOpInfo.propertiesOf op) where
  reprPrec := HasDialectOpInfo.propertiesRepr.reprPrec

instance [HasDialectOpInfo opCode] {op : opCode} : DecidableEq (HasDialectOpInfo.propertiesOf op) :=
  HasDialectOpInfo.propertiesDecideEq

instance [HasDialectOpInfo opCode] : DecidableEq opCode :=
  HasDialectOpInfo.decideEq

/--
The `HasOpInfo` type class provides the combined operation information for a
global opcode type.
-/
class HasOpInfo (opCode: Type)
    extends Hashable opCode, Repr opCode, Inhabited opCode, HasDialectOpInfo opCode

/--
`HasDialect OpInfo Dialect` states that `OpInfo` contains the operations from
`Dialect`.

It defines an injection from dialect-local opcodes to the combined opcode type, and
a projection from the combined opcode type to dialect-local opcodes.
The class also records that the dialect-local property family agree with the combined
property family on the injected opcodes.
-/
class HasDialect (OpInfo Dialect : Type) [HasOpInfo OpInfo] [HasDialectOpInfo Dialect] where
  /--
  Given a dialect opcode, get the equivalent opcode.
  `Veir.ofDialect` or a coercion should be used instead of calling this function.
  -/
  inject : Dialect → OpInfo
  /--
  Given a global opcode, get the equivalent dialect opcode, if it belongs to the dialect.
  `Veir.toDialect?` should be used instead of calling this function.
  -/
  project : OpInfo → Option Dialect
  /-- The equivalence between the project and inject functions. -/
  project_eq_some_iff (opInfo : OpInfo) (op : Dialect) :
    project opInfo = some op ↔ inject op = opInfo
  /-- The equivalence between the properties of the injected opcode and the dialect opcode. -/
  properties_eq (op : Dialect) :
    HasOpInfo.propertiesOf (inject op) = HasDialectOpInfo.propertiesOf op

/--
Project a global opcode to a dialect. Returns `none` when the opcode belongs
to another dialect.
-/
def toDialect? (Dialect : Type) {OpInfo : Type} [HasOpInfo OpInfo]
    [HasDialectOpInfo Dialect] [dialectInj : HasDialect OpInfo Dialect] (opInfo : OpInfo) :
    Option Dialect :=
  HasDialect.project opInfo

def ofDialect {Dialect : Type} (OpInfo : Type) [HasOpInfo OpInfo] [HasDialectOpInfo Dialect]
    [dialectInj : HasDialect OpInfo Dialect] (op : Dialect) :
    OpInfo :=
  HasDialect.inject op

/-- Coercion from a dialect opcode to the global opcode type. -/
instance {OpInfo : Type} {Dialect : Type} [HasOpInfo OpInfo] [HasDialectOpInfo Dialect]
    [HasDialect OpInfo Dialect] (op : Dialect) :
    CoeDep Dialect op OpInfo where
  coe := ofDialect OpInfo op

namespace HasDialect

variable {OpInfo : Type} {Dialect : Type} [HasOpInfo OpInfo] [HasDialectOpInfo Dialect]
  [dialectInj : HasDialect OpInfo Dialect]

/-- Projecting an injected dialect opcode recovers that opcode. -/
@[simp, grind =]
theorem toDialect?_ofDialect (op : Dialect) :
    toDialect? Dialect (ofDialect OpInfo op) = some op := by
  simp [ofDialect, toDialect?, HasDialect.project_eq_some_iff]

/-- A dialect's injection into an global opcode type is injective. -/
theorem ofDialect_injective {op₁ op₂ : Dialect} :
    ofDialect OpInfo op₁ = ofDialect OpInfo op₂ →
    op₁ = op₂ := by
  intro h
  grind [congrArg (toDialect? Dialect) h]

@[simp]
theorem toDialect?_eq_some_iff (opInfo : OpInfo) (op : Dialect) :
    toDialect? Dialect opInfo = some op ↔ ofDialect OpInfo op = opInfo := by
  grind [project_eq_some_iff, ofDialect, toDialect?]

grind_pattern toDialect?_eq_some_iff =>
  toDialect? Dialect opInfo, ofDialect OpInfo op

/-- Convert dialect-local properties to the global property family. -/
def ofDialectProperties (OpInfo : Type) [HasOpInfo OpInfo] [dialectInj : HasDialect OpInfo Dialect]
    (op : Dialect) (props : HasDialectOpInfo.propertiesOf op) :
    HasOpInfo.propertiesOf (opCode := OpInfo) op :=
  dialectInj.properties_eq op ▸ props

/-- Convert global properties of an injected opcode back to dialect-local properties. -/
def toDialectProperties (op : Dialect)
    (props : HasOpInfo.propertiesOf (opCode := OpInfo) op) :
    HasDialectOpInfo.propertiesOf op :=
  (dialectInj.properties_eq op).symm ▸ props

/-- Coercion from a dialect property to the global property type. -/
instance {OpInfo Dialect : Type} [HasOpInfo OpInfo] [HasDialectOpInfo Dialect]
    [HasDialect OpInfo Dialect] (x : Dialect) :
    CoeHead (HasOpInfo.propertiesOf (opCode := OpInfo) x)
      (HasDialectOpInfo.propertiesOf x) where
  coe := HasDialect.toDialectProperties x

/- Projecting an injected properties recover the original properties. -/
@[simp, grind =]
theorem toDialectProperties_ofDialectProperties (op : Dialect)
    (props : HasDialectOpInfo.propertiesOf op) :
    toDialectProperties op (ofDialectProperties OpInfo op props) =
      props := by
  grind [toDialectProperties, ofDialectProperties]

/-- A property injection into a combined property family in injective. -/
@[simp, grind =]
theorem ofDialectProperties_toDialectProperties (op : Dialect)
    (props : HasOpInfo.propertiesOf (opCode := OpInfo) op) :
    ofDialectProperties OpInfo op (toDialectProperties op props) =
      props := by
  grind [ofDialectProperties, toDialectProperties]

end HasDialect

instance [HasOpInfo opCode] {op : opCode} : Hashable (HasOpInfo.propertiesOf op) where
  hash := HasOpInfo.propertiesHash.hash

instance [HasOpInfo opCode] {op : opCode} : Inhabited (HasOpInfo.propertiesOf op) where
  default := HasOpInfo.propertiesDefault.default

instance [HasOpInfo opCode] {op : opCode} : Repr (HasOpInfo.propertiesOf op) where
  reprPrec := HasOpInfo.propertiesRepr.reprPrec

instance [HasOpInfo opCode] {op : opCode} : DecidableEq (HasOpInfo.propertiesOf op) :=
  HasOpInfo.propertiesDecideEq

instance [HasOpInfo opCode] : DecidableEq opCode :=
  HasOpInfo.decideEq

end -- public section

end Veir
