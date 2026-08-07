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
abbrev Materialized (OpInfo : Type) [HasOpInfo OpInfo] :=
  Σ op : OpInfo, HasOpInfo.propertiesOf op

/--
  Inject a dialect-local opcode and its properties into `OpInfo`. This is how a
  dialect materializer names the operation it wants created.
-/
def Materialized.of {OpInfo Dialect : Type} [HasOpInfo OpInfo] [HasOpInfo Dialect]
    [HasDialect OpInfo Dialect] (op : Dialect)
    (properties : HasOpInfo.propertiesOf op) : Materialized OpInfo :=
  ⟨ofDialect OpInfo op, HasDialect.ofDialectProperties OpInfo op properties⟩

end

end Veir
