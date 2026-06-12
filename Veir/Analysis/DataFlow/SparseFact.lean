module

public import Veir.Analysis.DataFlowFramework
public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

class SparseFactSpec (kind : FactKind) (Domain : outParam Type) where
  payloadEq : FactPayload kind = SparsePayload Domain

namespace SparseFact

variable {kind : FactKind} {Domain : Type}
variable [SparseFactSpec kind Domain]

private theorem payloadEq : FactPayload kind = SparsePayload Domain :=
  SparseFactSpec.payloadEq (kind := kind)

def getPayload (fact : Fact kind) : SparsePayload Domain :=
  cast payloadEq fact.payload

def setPayload (fact : Fact kind) (payload : SparsePayload Domain) : Fact kind :=
  { fact with payload := cast (Eq.symm payloadEq) payload }

def latticeElement (fact : Fact kind) : Domain :=
  (getPayload fact).latticeElement

def setLatticeElement (fact : Fact kind) (latticeElement : Domain) : Fact kind :=
  let payload := getPayload fact
  setPayload fact { payload with latticeElement := latticeElement }

/--
Propagate a sparse lattice update by revisiting dependents and all users of the
updated SSA value for subscribed analyses.
-/
def propagate (state : Fact kind) (anchor : LatticeAnchor) 
  (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := { dfCtx with workList := state.enqueueDependents dfCtx.workList }
  match anchor with
  | .ValuePtr ssaValue =>
    let mut maybeUse := ssaValue.getFirstUse! irCtx
    while let some use := maybeUse do
      let user := (use.get! irCtx).owner
      for analysisKind in state.subscribers do
        match InsertPoint.after? user irCtx with
        | some point =>
          dfCtx := dfCtx.enqueue (point, analysisKind)
        | none =>
          pure ()
      maybeUse := (use.get! irCtx).nextUse
  | _ =>
    pure ()
  dfCtx

section

variable [Bot Domain]

/-- Default sparse lattice fact for the given anchor. -/
def mkDefault : Fact kind :=
  { payload := cast (Eq.symm payloadEq) { latticeElement := ⊥ } }

instance : FactSpec kind where
  mkDefault := SparseFact.mkDefault (kind := kind)
  propagate := SparseFact.propagate (kind := kind)

end

def getElement? (kind : FactKind) [SparseFactSpec kind Domain] [FactSpec kind]
    (ssaValue : ValuePtr) (dfCtx : DataFlowContext) : Option Domain := do
  let state ← dfCtx.getFact? kind (.ValuePtr ssaValue)
  return latticeElement state

def getElementD (kind : FactKind) [SparseFactSpec kind Domain] [FactSpec kind]
    (ssaValue : ValuePtr) (fallback : Domain)
    (dfCtx : DataFlowContext) : Domain :=
  (getElement? kind ssaValue dfCtx).getD fallback

end SparseFact

end Veir
