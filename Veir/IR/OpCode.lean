module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

class IsOpCode (opCode : Type) extends Hashable opCode, Repr opCode, Inhabited opCode where
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

abbrev propertiesOf {OpCode : Type} [IsOpCode OpCode] (opCode : OpCode) :=
  IsOpCode.propertiesOf opCode

instance [IsOpCode OpCode] {op : OpCode} : Hashable (propertiesOf op) where
  hash := IsOpCode.propertiesHash.hash

instance [IsOpCode OpCode] {op : OpCode} : Inhabited (propertiesOf op) where
  default := IsOpCode.propertiesDefault.default

instance [IsOpCode OpCode] {op : OpCode} : Repr (propertiesOf op) where
  reprPrec := IsOpCode.propertiesRepr.reprPrec

instance [IsOpCode OpCode] {op : OpCode} : DecidableEq (propertiesOf op) :=
  IsOpCode.propertiesDecideEq

instance [IsOpCode OpCode] : DecidableEq OpCode :=
  IsOpCode.decideEq

/--
`HasDialect OpInfo Dialect` states that `OpInfo` contains the operations from
`Dialect`.

It defines an injection from dialect-local opcodes to the combined opcode type, and
a projection from the combined opcode type to dialect-local opcodes.
The class also records that the dialect-local property family agree with the combined
property family on the injected opcodes.
-/
class HasDialect (OpInfo Dialect : Type) [IsOpCode OpInfo] [IsOpCode Dialect] where
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
    propertiesOf (inject op) = propertiesOf op

/--
Project a global opcode to a dialect. Returns `none` when the opcode belongs
to another dialect.
-/
def toDialect? (Dialect : Type) {OpInfo : Type} [IsOpCode OpInfo]
    [IsOpCode Dialect] [dialectInj : HasDialect OpInfo Dialect] (opInfo : OpInfo) :
    Option Dialect :=
  HasDialect.project opInfo

def ofDialect {Dialect : Type} (OpInfo : Type) [IsOpCode OpInfo] [IsOpCode Dialect]
    [dialectInj : HasDialect OpInfo Dialect] (op : Dialect) :
    OpInfo :=
  HasDialect.inject op

/--
We can always treat a global opcode type as a dialect of itself.
This simplifies quite a lot of the API, since we can use a single generic function for both
dialect-local and global opcodes.
-/
instance hasDialectRefl (OpInfo : Type) [IsOpCode OpInfo] : HasDialect OpInfo OpInfo where
  inject := id
  project := some
  project_eq_some_iff _ _ := by grind
  properties_eq _ := rfl

/-- Casting an opcode to itself is the identity. -/
@[simp, grind =]
theorem ofDialect_hasDialectRefl (OpInfo : Type) [IsOpCode OpInfo] (op : OpInfo) :
    ofDialect OpInfo op = op := by rfl

/-- Coercion from a dialect opcode to the global opcode type. -/
instance {OpInfo : Type} {Dialect : Type} [IsOpCode OpInfo] [IsOpCode Dialect]
    [HasDialect OpInfo Dialect] (op : Dialect) :
    CoeDep Dialect op OpInfo where
  coe := ofDialect OpInfo op

namespace HasDialect

variable {OpInfo : Type} {Dialect : Type} [IsOpCode OpInfo] [IsOpCode Dialect]
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

/-- Equal global opcodes have equal dialect-local property types. -/
theorem properties_eq_of_ofDialect_eq
    {Dialect₁ Dialect₂ : Type}
    [IsOpCode Dialect₁] [IsOpCode Dialect₂]
    [hasDialect₁ : HasDialect OpInfo Dialect₁]
    [hasDialect₂ : HasDialect OpInfo Dialect₂]
    {op₁ : Dialect₁} {op₂ : Dialect₂}
    (h : ofDialect OpInfo op₁ = ofDialect OpInfo op₂) :
    propertiesOf op₁ = propertiesOf op₂ := by
  simp [← hasDialect₁.properties_eq op₁, ← hasDialect₂.properties_eq op₂]
  grind [ofDialect]

@[simp]
theorem toDialect?_eq_some_iff (opInfo : OpInfo) (op : Dialect) :
    toDialect? Dialect opInfo = some op ↔ ofDialect OpInfo op = opInfo := by
  grind [project_eq_some_iff, ofDialect, toDialect?]

grind_pattern toDialect?_eq_some_iff =>
  toDialect? Dialect opInfo, ofDialect OpInfo op

/-- Convert dialect-local properties to the global property family. -/
def ofDialectProperties (OpInfo : Type) [IsOpCode OpInfo] [dialectInj : HasDialect OpInfo Dialect]
    (op : Dialect) (props : propertiesOf op) :
    propertiesOf (OpCode := OpInfo) op :=
  dialectInj.properties_eq op ▸ props

/-- Convert global properties of an injected opcode back to dialect-local properties. -/
def toDialectProperties (op : Dialect)
    (props : propertiesOf (OpCode := OpInfo) op) :
    propertiesOf op :=
  (dialectInj.properties_eq op).symm ▸ props

@[simp, grind =]
theorem toDialectProperties_cast_ofDialectProperties_eq
    {Dialect₁ Dialect₂ : Type}
    [IsOpCode Dialect₁] [IsOpCode Dialect₂]
    [hasDialect₁ : HasDialect OpInfo Dialect₁]
    [hasDialect₂ : HasDialect OpInfo Dialect₂]
    {op₁ : Dialect₁} {op₂ : Dialect₂}
    (h : ofDialect OpInfo op₁ = ofDialect OpInfo op₂)
    (props : propertiesOf op₁) :
    toDialectProperties op₂ (h ▸ ofDialectProperties OpInfo op₁ props) =
      properties_eq_of_ofDialect_eq h ▸ props := by
  apply eq_of_heq
  exact (cast_heq _ _).trans ((eqRec_heq h _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- Coercion from a dialect property to the global property type. -/
instance {OpInfo Dialect : Type} [IsOpCode OpInfo] [IsOpCode Dialect]
    [HasDialect OpInfo Dialect] (x : Dialect) :
    CoeHead (propertiesOf (OpCode := OpInfo) x)
      (propertiesOf x) where
  coe := HasDialect.toDialectProperties x

/- Projecting an injected properties recover the original properties. -/
@[simp, grind =]
theorem toDialectProperties_ofDialectProperties (op : Dialect)
    (props : propertiesOf op) :
    toDialectProperties op (ofDialectProperties OpInfo op props) =
      props := by
  grind [toDialectProperties, ofDialectProperties]

/-- A property injection into a combined property family in injective. -/
@[simp, grind =]
theorem ofDialectProperties_toDialectProperties (op : Dialect)
    (props : propertiesOf (OpCode := OpInfo) op) :
    ofDialectProperties OpInfo op (toDialectProperties op props) =
      props := by
  grind [ofDialectProperties, toDialectProperties]

end HasDialect

end -- public section

end Veir
