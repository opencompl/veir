module

public import Veir.IR.OpInfo
public import Veir.RuntimeValue

/-!
  # Constant materialization
-/

namespace Veir

public section

/--
  A constant-like operation together with the properties that make it
  materialize a particular value.
-/
abbrev Materialized (OpInfo : Type) [IsOpCode OpInfo] :=
  Σ op : OpInfo, propertiesOf op

/--
  Inject a dialect-local opcode and its properties into `OpInfo`. This is how a
  dialect materializer names the operation it wants created.
-/
def Materialized.of {OpInfo Dialect : Type} [IsOpCode OpInfo] [IsOpCode Dialect]
    [HasDialect OpInfo Dialect] (op : Dialect)
    (properties : propertiesOf op) : Materialized OpInfo :=
  ⟨ofDialect OpInfo op, HasDialect.ofDialectProperties OpInfo op properties⟩

end

end Veir
