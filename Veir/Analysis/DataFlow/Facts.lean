module

public import Std.Data.HashMap
public import Init.Data.Queue
public import Veir.IR.Basic
public import Veir.GlobalOpInfo
public import Veir.Rewriter.InsertPoint

open Std (HashMap Queue)

public section

namespace Veir

/-!
# Facts in the dataflow framework

In the mathematics of monotone dataflow frameworks, an analysis assigns abstract
states (each from some lattice) to program points and repeatedly applies monotone
transfer functions until a fixpoint is reached. A fixpoint `f` is such that 
`f(x) = x`. So in other words, when nothing changes.

This file defines the objects used to store those abstract states. A
`Fact` is one piece of analysis information and a `LatticeAnchor` says 
where in the IR that information lives (such as an SSA value or a CFG 
edge).
-/

/--
A directed control flow edge between two blocks.
-/
structure CFGEdge where
  source : BlockPtr
  target : BlockPtr
deriving BEq, Hashable

/--
The control flow graph positions and SSA values where dataflow facts are attached.
-/
inductive LatticeAnchor
  | InsertPoint (point : InsertPoint)
  | ValuePtr (value : ValuePtr)
  | CFGEdge (edge : CFGEdge)
deriving BEq, Hashable

instance : Coe InsertPoint LatticeAnchor where
  coe := .InsertPoint

/-!
# Analyses and facts
-/

/--
Tags to match on for different `DataFlowAnalysis` types.
-/
inductive AnalysisKind where
  | dominance
deriving BEq, Hashable, Repr, DecidableEq

/--
Tags to match on for different fact types.
-/
inductive FactKind where
  | dominator
  | regionMetadata
deriving BEq, ReflBEq, LawfulBEq, Hashable, Repr, DecidableEq

abbrev WorkItem := InsertPoint × AnalysisKind
abbrev WorkList := Queue WorkItem

/--
The immediate dominator fact attached to a block entry.
-/
structure DominatorPayload where
  iDom : Option BlockPtr := none

/--
Caches the post ordering of a region's blocks.

Stored in the entry block of each region.
-/
structure RegionMetadataPayload where
  postOrderIndex : HashMap BlockPtr Nat := {}

/--
A sparse dataflow fact payload for one abstract domain.
-/
structure SparsePayload (Domain : Type) where
  useDefSubscribers : Array AnalysisKind := #[]
  latticeElement : Domain

/--
The fact specific data stored for each fact kind.
-/
@[expose] def FactPayload : FactKind → Type
  | .dominator => DominatorPayload
  | .regionMetadata => RegionMetadataPayload

/--
A dataflow fact stored by the framework.

Each fact associates with a lattice anchor (some location in the program), has
an array of dependents (other facts that "depend" on this fact's current state in
some fashion), has an array of analysis subscribers (similar to dependents except 
it's entire analyses that depend on this fact's current state), and has the fact 
specific payload determined by its `FactKind`.
-/
structure Fact (kind : FactKind) where
  dependents : Array WorkItem := #[]
  subscribers : Array AnalysisKind := #[]
  payload : FactPayload kind

namespace Fact

/--
Set the fact's dependents.
-/
def setDependents (fact : Fact kind) (dependents : Array WorkItem) : Fact kind :=
  { fact with dependents := dependents }

/--
Add one dependent work item to the fact.
-/
def addDependent (fact : Fact kind) (workItem : WorkItem) : Fact kind :=
  fact.setDependents (fact.dependents.push workItem)

/--
Subscribe one analysis to changes of this fact.
-/
def subscribe (fact : Fact kind) (analysisKind : AnalysisKind) : Fact kind :=
  if fact.subscribers.contains analysisKind then
    fact
  else
    { fact with subscribers := (fact.subscribers.push analysisKind) }

/--
Enqueue all dependents of this fact.
-/
def enqueueDependents (fact : Fact kind) (workList : WorkList) : WorkList :=
  Id.run do
    let mut workList := workList
    for workItem in fact.dependents do
      workList := workList.enqueue workItem
    workList

def iDom (fact : Fact .dominator) : Option BlockPtr :=
  fact.payload.iDom

def setIDom (fact : Fact .dominator) (iDom : Option BlockPtr) : Fact .dominator :=
  { fact with payload := { fact.payload with iDom := iDom } }

def postOrderIndex (fact : Fact .regionMetadata) : HashMap BlockPtr Nat :=
  fact.payload.postOrderIndex

def setPostOrderIndex (fact : Fact .regionMetadata)
    (postOrderIndex : HashMap BlockPtr Nat) : Fact .regionMetadata :=
  { fact with payload := { fact.payload with postOrderIndex := postOrderIndex } }

end Fact

abbrev DominatorFact := Fact .dominator

abbrev RegionMetadataFact := Fact .regionMetadata

end Veir
