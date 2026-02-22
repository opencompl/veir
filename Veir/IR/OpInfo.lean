module

namespace Veir

/--
Define a typeclass hasProperties
-/
public class OpInfo (opCodeTy : Type)
    extends Hashable opCodeTy, Repr opCodeTy, Inhabited opCodeTy where
  propertiesOf : opCodeTy → Type
  propertiesHash {opCode : opCodeTy} : Hashable (propertiesOf opCode)
  propertiesDefault {opCode : opCodeTy} : Inhabited (propertiesOf opCode)
  propertiesRepr {opCode : opCodeTy} : Repr (propertiesOf opCode)
  propertiesDecideableEq {opCode : opCodeTy} : DecidableEq (propertiesOf opCode)
  decideableEq : DecidableEq (opCodeTy)

end Veir
