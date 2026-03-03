module

public import Std.Data.HashMap
public import Init.Data.Queue
public import Veir.Analysis.DataFlow.Domains
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
`f(x) = x`. In other words, when nothing changes.

This file defines the objects used to store those abstract states. A
`Fact` is one piece of analysis information and a `LatticeAnchor` says 
where in the IR that information lives (such as an SSA value or a CFG 
edge).
-/

namespace InsertPoint

/--
Return whether the insertion point is at the beginning of a block.
-/
def isBlockStart (point : InsertPoint) (irCtx : IRContext OpCode) : Bool :=
  match point with
  | .before op =>
    match (op.get! irCtx).parent with
    | some block => (block.get! irCtx).firstOp == some op
    | none => false
  | .atEnd block => (block.get! irCtx).firstOp == none

end InsertPoint

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

/-!
# Analyses and facts
-/

/--
Tags to match on for different `DataFlowAnalysis` types.
-/
inductive AnalysisKind where
  | sparseConstantPropagation
  | deadCode
deriving BEq, Hashable, Repr, DecidableEq

/--
Tags to match on for different fact types.
-/
inductive FactKind where
  | executable
  | sparseConstant
deriving BEq, ReflBEq, LawfulBEq, Hashable, Repr, DecidableEq

abbrev WorkItem := InsertPoint × AnalysisKind
abbrev WorkList := Queue WorkItem

/--
Tracks whether a control flow point or edge is executable.
-/
structure ExecutablePayload where
  live : Bool := false
  subscribers : Array AnalysisKind := #[]

/--
A sparse dataflow fact payload for one abstract domain.
-/
structure SparsePayload (Domain : Type) where
  useDefSubscribers : Array AnalysisKind := #[]
  latticeElement : Domain

/--
The fact specific data stored for each fact kind.
-/
@[expose] def FactPayload : FactKind -> Type
  | .executable => ExecutablePayload
  | .sparseConstant => SparsePayload ConstantDomain

/--
A dataflow fact stored by the framework.

Each fact carries a lattice anchor (some location in the program this fact
associates with), an array of dependents (other facts that "depend" on this fact's
current state in some fashion), and the fact specific payload determined by its
`FactKind`.
-/
structure Fact (kind : FactKind) where
  anchor : LatticeAnchor
  dependents : Array WorkItem := #[]
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
Enqueue all dependents of this fact.
-/
def enqueueDependents (fact : Fact kind) (workList : WorkList) : WorkList :=
  Id.run do
    let mut workList := workList
    for workItem in fact.dependents do
      workList := workList.enqueue workItem
    workList

def live (fact : Fact .executable) : Bool :=
  fact.payload.live

def subscribers (fact : Fact .executable) : Array AnalysisKind :=
  fact.payload.subscribers

def setLive (fact : Fact .executable) (live : Bool) : Fact .executable :=
  { fact with payload := { fact.payload with live := live } }

def setSubscribers (fact : Fact .executable) (subscribers : Array AnalysisKind) : Fact .executable :=
  { fact with payload := { fact.payload with subscribers := subscribers } }

def setToLive (fact : Fact .executable) : Fact .executable :=
  fact.setLive true

def blockContentSubscribe (fact : Fact .executable) (analysisKind : AnalysisKind) : Fact .executable :=
  if fact.subscribers.contains analysisKind then
    fact
  else
    fact.setSubscribers (fact.subscribers.push analysisKind)

end Fact

abbrev ExecutableFact := Fact .executable

end Veir
