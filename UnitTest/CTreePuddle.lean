import Veir.PatternRewriter.Puddle.CTreeValidityTactics

open Veir Veir.Puddle

namespace CTreePuddleTest

/-- Recreating a nondeterministic operation must allow the source choice to depend on the target. -/
private def recreateFreeze : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.llvm .freeze) #[x] #[ty]
      return (ty, x, root.properties))
    (fun (ty, x, prop) => CreateProg.operation (.llvm .freeze) #[x] #[ty] prop)
    (fun result => result)

set_option warn.sorry false in
example : CTree.Pattern.Valid recreateFreeze := by
  unfold recreateFreeze
  simpPuddleValid
  sorry

/-- A created terminator is rejected by the static support check. -/
private def createReturnBeforeFreeze : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.llvm .freeze) #[x] #[ty]
      return (ty, x, root.properties))
    (fun (ty, x, prop) => do
      let returnProp ← CreateProg.property (.llvm .return) ()
      let _ ← CreateProg.operation (.llvm .return) #[] #[] returnProp
      CreateProg.operation (.llvm .freeze) #[x] #[ty] prop)
    (fun result => result)

example : ¬ CTree.Pattern.Supported createReturnBeforeFreeze := by
  unfold createReturnBeforeFreeze
  unfoldPuddleBuilder
  simp [CTree.Pattern.Supported, get_effects, is_terminator]

/--
Rewrite `freeze (add x y)` to `add (freeze x) (freeze y)` for wrapping addition.
Match two operations and create three, with independent choices for the two new freezes.
-/
private def freezeAdd : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let add ← MatchProg.operation (.llvm .add) #[x, y] #[ty]
        (fun properties => properties == { nsw := false, nuw := false })
      let root ← MatchProg.root (.llvm .freeze) #[add.res[0]!] #[ty]
      return (ty, x, y, add.properties, root.properties))
    (fun (ty, x, y, addProp, freezeProp) => do
      let fx ← CreateProg.operation (.llvm .freeze) #[x] #[ty] freezeProp
      let fy ← CreateProg.operation (.llvm .freeze) #[y] #[ty] freezeProp
      CreateProg.operation (.llvm .add) #[fx.res[0]!, fy.res[0]!] #[ty] addProp)
    (fun result => result)

set_option warn.sorry false in
example : CTree.Pattern.Valid freezeAdd := by
  unfold freezeAdd
  simpPuddleValid
  sorry

end CTreePuddleTest

namespace CTreeStatefulPuddleTest

/-- Replace a load with another load. -/
private def recreateLoad : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let ptr ← MatchProg.value ptrTy
      let root ← MatchProg.root (.llvm .load) #[ptr] #[ty]
      return (ty, ptr, root.properties))
    (fun (ty, ptr, prop) => CreateProg.operation (.llvm .load) #[ptr] #[ty] prop)
    (fun result => result)

/- Memory effects are allowed on both sides of a rewrite. -/
example : CTree.Pattern.Supported recreateLoad := by
  unfold recreateLoad
  unfoldPuddleBuilder
  simp [CTree.Pattern.Supported, get_effects, is_terminator]

set_option warn.sorry false in
example : CTree.Pattern.Valid recreateLoad := by
  unfold recreateLoad
  simpPuddleValid
  sorry

end CTreeStatefulPuddleTest

namespace CTreeMatchPurityTest

private def matchTwoLoads : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let ptr ← MatchProg.value ptrTy
      let _ ← MatchProg.operation (.llvm .load) #[ptr] #[ty]
      let root ← MatchProg.root (.llvm .load) #[ptr] #[ty]
      return (ty, ptr, root.properties))
    (fun (ty, ptr, prop) => CreateProg.operation (.llvm .load) #[ptr] #[ty] prop)
    (fun result => result)

/- An effectful non-root match is supported: a pattern only reuses its results, so it keeps
running as before (see `CTree.CanInterpretTo`). -/
example : CTree.Pattern.Supported matchTwoLoads := by
  unfold matchTwoLoads
  unfoldPuddleBuilder
  simp [CTree.Pattern.Supported, is_terminator]

end CTreeMatchPurityTest
