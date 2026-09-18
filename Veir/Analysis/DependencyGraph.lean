module

public import Std.Data.HashMap
public import Std.Data.HashSet

open Std (HashMap HashSet)

public section

namespace Veir

/--
A bidirectional dependency graph.

`dependencies` maps each dependent to the objects it reads, while `dependents`
stores the reverse edges used to find what must be revisited after a change.
-/
structure DependencyGraph (Dependency Dependent : Type)
    [BEq Dependency] [Hashable Dependency] [BEq Dependent] [Hashable Dependent] where
  dependencies : HashMap Dependent (HashSet Dependency)
  dependents : HashMap Dependency (HashSet Dependent)

namespace DependencyGraph

variable [BEq Dependency] [Hashable Dependency]
variable [BEq Dependent] [Hashable Dependent]

/-- An empty dependency graph. -/
def empty : DependencyGraph Dependency Dependent :=
  { dependencies := ∅
    dependents := ∅ }

variable [LawfulBEq Dependency] [LawfulBEq Dependent]

/-- Return the objects read by `dependent`. -/
def getDependencies
    (graph : DependencyGraph Dependency Dependent)
    (dependent : Dependent) : HashSet Dependency :=
  graph.dependencies.getD dependent ∅

/-- Return the objects that read `dependency`. -/
def getDependents
    (graph : DependencyGraph Dependency Dependent)
    (dependency : Dependency) : HashSet Dependent :=
  graph.dependents.getD dependency ∅

/--
Replace every dependency of `dependent`, updating only edges that changed in
both directions of the graph.
-/
def setDependencies
    (graph : DependencyGraph Dependency Dependent)
    (dependent : Dependent)
    (newDependencies : HashSet Dependency) : DependencyGraph Dependency Dependent := Id.run do
  let oldDependencies := graph.getDependencies dependent

  -- Preserve the original graph when the relation did not change.
  if oldDependencies == newDependencies then
    return graph

  let mut dependents := graph.dependents

  -- Stop listing `dependent` as a dependent of each dependency it no longer has.
  for dependency in oldDependencies do
    if newDependencies.contains dependency then
      continue
    dependents := dependents.alter dependency fun
      | none => none
      | some current =>
        let remaining := current.erase dependent
        if remaining.isEmpty then none else some remaining

  -- List `dependent` as a dependent of each newly added dependency. Dependencies
  -- that `dependent` already had do not need to be updated.
  for dependency in newDependencies do
    if oldDependencies.contains dependency then
      continue
    dependents := dependents.alter dependency fun
      | none => some {dependent}
      | some current => some (current.insert dependent)

  -- Store the exact set of dependencies of `dependent`. Omit the entry when that
  -- set is empty so the dependencies map remains sparse.
  let dependencies :=
    if newDependencies.isEmpty then graph.dependencies.erase dependent
    else graph.dependencies.insert dependent newDependencies
  { dependencies, dependents }

/-- Add one dependency while keeping both directions of the graph synchronized. -/
def addDependency
    (graph : DependencyGraph Dependency Dependent)
    (dependent : Dependent)
    (dependency : Dependency) : DependencyGraph Dependency Dependent :=
  let dependencies := graph.getDependencies dependent
  if dependencies.contains dependency then
    graph
  else
    { dependencies := graph.dependencies.alter dependent fun
        | none => some {dependency}
        | some current => some (current.insert dependency)
      dependents := graph.dependents.alter dependency fun
        | none => some {dependent}
        | some current => some (current.insert dependent) }

/-- Remove every dependency of `dependent`. -/
def clearDependencies
    (graph : DependencyGraph Dependency Dependent)
    (dependent : Dependent) : DependencyGraph Dependency Dependent :=
  graph.setDependencies dependent ∅

end DependencyGraph

end Veir
