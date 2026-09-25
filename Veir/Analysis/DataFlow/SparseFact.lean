module

public import Veir.Analysis.DataFlowFramework
public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/--
Implement this class to register a custom type to be recognized as
a sparse fact type by the dataflow framework.
-/
class SparseFactSpec (kind : FactKind) (Domain : outParam Type) where
  Metadata : Type
  [metadataInhabited : Inhabited Metadata]
  metadataOfResult : OpCode → Domain → Metadata :=
    fun _ _ => metadataInhabited.default
  payloadEq : FactPayload kind = SparsePayload Domain Metadata

instance SparseFactSpec.instInhabitedMetadata
    {kind : FactKind} {Domain : Type} [spec : SparseFactSpec kind Domain] :
    Inhabited spec.Metadata :=
  spec.metadataInhabited

namespace SparseFact

variable {kind : FactKind} {Domain : Type}
variable [spec : SparseFactSpec kind Domain]

def getPayload (fact : Fact kind) : SparsePayload Domain spec.Metadata :=
  cast SparseFactSpec.payloadEq fact.payload

def setPayload (fact : Fact kind) (payload : SparsePayload Domain spec.Metadata) :
    Fact kind :=
  { fact with payload := cast (Eq.symm SparseFactSpec.payloadEq) payload }

def latticeElement (fact : Fact kind) : Domain :=
  (getPayload fact).latticeElement

def mkPayload (latticeElement : Domain) (metadata : spec.Metadata := default) :
    SparsePayload Domain spec.Metadata :=
  { latticeElement, metadata }

/--
Propagate a sparse lattice update by revisiting dependents and all users of the
updated SSA value for subscribed analyses.
-/
def propagate (state : Fact kind) (anchor : LatticeAnchor) 
  (dfCtx : DataFlowContext) (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := { dfCtx with workList := state.enqueueDependents dfCtx.workList }
  match anchor with
  | .ValuePtr ssaValue =>
    let mut maybeUse := ssaValue.getFirstUse! irCtx.raw
    while let some use := maybeUse do
      let user := (use.get! irCtx.raw).owner
      match InsertPoint.after? user irCtx.raw with
      | some point =>
        for analysisKind in state.subscribers do
          dfCtx := dfCtx.enqueue (point, analysisKind)
      | none => pure ()
      maybeUse := (use.get! irCtx.raw).nextUse
  | _ =>
    pure ()
  dfCtx

section

variable [Bot Domain]

/-- Default sparse lattice fact for the given anchor. -/
def mkDefault : Fact kind :=
  { payload := cast (Eq.symm SparseFactSpec.payloadEq) (mkPayload (kind := kind) ⊥) }

instance : FactSpec kind where
  mkDefault := SparseFact.mkDefault (kind := kind)
  propagate := SparseFact.propagate (kind := kind)

end

def getElement (kind : FactKind) [SparseFactSpec kind Domain] [FactSpec kind]
    [Bot Domain] (ssaValue : ValuePtr) (dfCtx : DataFlowContext) : Domain :=
  match dfCtx.getFact? kind (.ValuePtr ssaValue) with
  | some state => latticeElement state
  | none => ⊥

end SparseFact

end Veir
