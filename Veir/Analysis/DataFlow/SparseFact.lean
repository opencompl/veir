module

public import Veir.Analysis.DataFlowFramework

public section

namespace Veir

/-! ## Sparse lattice facts -/

class SparseFactSpec (kind : FactKind) (Domain : outParam Type) where
  payloadEq : FactPayload kind = SparsePayload Domain

abbrev SparseDomain (kind : FactKind) [SparseFactSpec kind Domain] : Type :=
  Domain

namespace SparseFact

variable {kind : FactKind} {Domain : Type}
variable [SparseFactSpec kind Domain] [LatticeElement Domain]

private def payloadEq : FactPayload kind = SparsePayload Domain :=
  SparseFactSpec.payloadEq (kind := kind)

def getPayload (fact : Fact kind) : SparsePayload Domain :=
  cast payloadEq fact.payload

def setPayload (fact : Fact kind) (payload : SparsePayload Domain) : Fact kind :=
  { fact with payload := cast (Eq.symm payloadEq) payload }

def useDefSubscribers (fact : Fact kind) : Array AnalysisKind :=
  (getPayload fact).useDefSubscribers

def latticeElement (fact : Fact kind) : Domain :=
  (getPayload fact).latticeElement

def setLatticeElement (fact : Fact kind) (latticeElement : Domain) : Fact kind :=
  let payload := getPayload fact
  setPayload fact { payload with latticeElement := latticeElement }

/-- Default sparse lattice fact for the given anchor. -/
def mkDefault (anchor : LatticeAnchor) : Fact kind :=
  { anchor := anchor
    dependents := #[]
    payload := cast (Eq.symm payloadEq)
      { useDefSubscribers := #[]
        latticeElement := LatticeElement.bottom } }

/--
Propagate a sparse lattice update by revisiting dependents and all users of the
updated SSA value for subscribed analyses.
-/
def propagate (state : Fact kind) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := { dfCtx with workList := state.enqueueDependents dfCtx.workList }
  match state.anchor with
  | .ValuePtr ssaValue =>
    let mut maybeUse := ssaValue.getFirstUse! irCtx
    while h : maybeUse.isSome do
      let use := maybeUse.get h
      let user := (use.get! irCtx).owner
      for analysisKind in useDefSubscribers state do
        match InsertPoint.after? user irCtx with
        | some point =>
          dfCtx := dfCtx.enqueue (point, analysisKind)
        | none =>
          pure ()
      maybeUse := (use.get! irCtx).nextUse
  | _ =>
    pure ()
  dfCtx

def useDefSubscribe (state : Fact kind)
    (analysisKind : AnalysisKind) : Fact kind :=
  let payload := getPayload state
  if payload.useDefSubscribers.contains analysisKind then
    state
  else
    setPayload state { payload with useDefSubscribers := payload.useDefSubscribers.push analysisKind }

instance : FactSpec kind where
  mkDefault := SparseFact.mkDefault (kind := kind)
  propagate := SparseFact.propagate (kind := kind)

def getElement? (kind : FactKind) [SparseFactSpec kind Domain] [LatticeElement Domain]
    (dfCtx : DataFlowContext) (ssaValue : ValuePtr) : Option Domain := do
  let state ← dfCtx.getFact? kind (.ValuePtr ssaValue)
  return latticeElement state

def getElementD (kind : FactKind) [SparseFactSpec kind Domain] [LatticeElement Domain]
    (dfCtx : DataFlowContext) (ssaValue : ValuePtr)
    (fallback : Domain) : Domain :=
  match getElement? kind dfCtx ssaValue with
  | some latticeValue =>
    latticeValue
  | none =>
    fallback

end SparseFact

end Veir
