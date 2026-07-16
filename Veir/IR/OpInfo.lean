module

namespace Veir

public section

class HasDialectOpInfo (opCode: Type)
    extends Hashable opCode, Repr opCode, Inhabited opCode where
  propertiesOf : opCode → Type
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
The `HasOpInfo` type class provides information about opcodes and their properties
and how to hash, represent, and compare them for equality. It also contains the mapping between
opcodes and whether or not their regions have SSA dominance.
-/
class HasOpInfo (opCode: Type)
    extends Hashable opCode, Repr opCode, Inhabited opCode, HasDialectOpInfo opCode where
  moduleOpCode: opCode
  /--
  Whether definitions in the indexed region must dominate their uses. A false
  result denotes graph-style semantics, where only a single block can be in the
  region, and operation order does not impose SSA dominance.
  -/
  hasSSADominance : opCode → Nat → Bool

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
