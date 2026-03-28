import Veir.Rewriter.LinkedList.Basic
import Veir.Properties

open Veir

/-!
  Tests for cycle prevention in `setParentWithCheck!`.

  Tests `OperationPtr.containsBlock!`, `BlockPtr.containsRegion!`,
  and the cycle checks added to `setParentWithCheck!`.

  IR tree hierarchy: Operation → Region → Block → Operation → ...
  Parent pointers go upward: Block.parent → Region, Region.parent → Operation, Operation.parent → Block
-/

/-- Build a one-level IR tree: op0 → region0 → block0.
    op0 has no parent (root). All parent pointers are set. -/
private def buildSimpleTree : Option (IRContext OpCode × OperationPtr × RegionPtr × BlockPtr) := do
  let (ctx, op0) ← OperationPtr.allocEmpty (IRContext.empty OpCode) .builtin_module default
  let (ctx, region0) ← RegionPtr.allocEmpty ctx
  let (ctx, block0) ← BlockPtr.allocEmpty ctx
  let ctx := op0.pushRegion! ctx region0
  let ctx := region0.setParent! ctx op0
  let ctx := block0.setParent! ctx (some region0)
  return (ctx, op0, region0, block0)

/-- Build a two-level IR tree:
    op0 → region0 → block0 → op1 → region1 → block1
    op0 is the root (no parent). op1's parent is block0. -/
private def buildDeepTree :
    Option (IRContext OpCode × OperationPtr × RegionPtr × BlockPtr ×
            OperationPtr × RegionPtr × BlockPtr) := do
  let (ctx, op0) ← OperationPtr.allocEmpty (IRContext.empty OpCode) .builtin_module default
  let (ctx, region0) ← RegionPtr.allocEmpty ctx
  let (ctx, block0) ← BlockPtr.allocEmpty ctx
  let ctx := op0.pushRegion! ctx region0
  let ctx := region0.setParent! ctx op0
  let ctx := block0.setParent! ctx (some region0)
  let (ctx, op1) ← OperationPtr.allocEmpty ctx .builtin_module default
  let (ctx, region1) ← RegionPtr.allocEmpty ctx
  let (ctx, block1) ← BlockPtr.allocEmpty ctx
  let ctx := op1.pushRegion! ctx region1
  let ctx := region1.setParent! ctx op1
  let ctx := block1.setParent! ctx (some region1)
  let ctx := op1.setParent! ctx (some block0)
  return (ctx, op0, region0, block0, op1, region1, block1)

/-! ## OperationPtr.containsBlock! -/

-- op0 directly contains block0 (op0 → region0 → block0)
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, op0, _, block0) ← buildSimpleTree
  return op0.containsBlock! ctx block0

-- op0 transitively contains block1 (op0 → region0 → block0 → op1 → region1 → block1)
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, op0, _, _, _, _, block1) ← buildDeepTree
  return op0.containsBlock! ctx block1

-- op1 directly contains block1
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, _, _, _, op1, _, block1) ← buildDeepTree
  return op1.containsBlock! ctx block1

-- op1 does NOT contain block0 (block0 is an ancestor of op1)
/--
info: some false
-/
#guard_msgs in
#eval do
  let (ctx, _, _, block0, op1, _, _) ← buildDeepTree
  return op1.containsBlock! ctx block0

-- op0 does NOT contain a freshly allocated block (no parent pointers)
/--
info: some false
-/
#guard_msgs in
#eval do
  let (ctx, op0, _, _) ← buildSimpleTree
  let (ctx, freshBlock) ← BlockPtr.allocEmpty ctx
  return op0.containsBlock! ctx freshBlock

/-! ## BlockPtr.containsRegion! -/

-- block0 transitively contains region1 (block0 → op1 → region1)
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, _, _, block0, _, region1, _) ← buildDeepTree
  return block0.containsRegion! ctx region1

-- block1 does NOT contain region0 (region0 is an ancestor of block1)
/--
info: some false
-/
#guard_msgs in
#eval do
  let (ctx, _, region0, _, _, _, block1) ← buildDeepTree
  return block1.containsRegion! ctx region0

-- block0 does NOT contain a freshly allocated region (no parent pointers)
/--
info: some false
-/
#guard_msgs in
#eval do
  let (ctx, _, _, block0, _, _, _) ← buildDeepTree
  let (ctx, freshRegion) ← RegionPtr.allocEmpty ctx
  return block0.containsRegion! ctx freshRegion

/-! ## OperationPtr.setParentWithCheck! (cycle rejection) -/

-- Cycle: op0 contains block0, so setting block0 as op0's parent should fail
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, op0, _, block0) ← buildSimpleTree
  return (op0.setParentWithCheck! ctx block0).isNone

-- Cycle: op0 transitively contains block1, so setting block1 as op0's parent should fail
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, op0, _, _, _, _, block1) ← buildDeepTree
  return (op0.setParentWithCheck! ctx block1).isNone

-- Valid: op0 has no parent and freshBlock is not inside op0 → should succeed
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, op0, _, _) ← buildSimpleTree
  let (ctx, freshBlock) ← BlockPtr.allocEmpty ctx
  return (op0.setParentWithCheck! ctx freshBlock).isSome

-- Existing parent: op1 already has parent block0 → should fail even without cycle
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, _, _, _, op1, _, _) ← buildDeepTree
  let (ctx, freshBlock) ← BlockPtr.allocEmpty ctx
  return (op1.setParentWithCheck! ctx freshBlock).isNone

/-! ## BlockPtr.setParentWithCheck! (cycle rejection) -/

-- Cycle: block0 contains region1, so setting region1 as block0's parent should fail
-- (block0 already has a parent too, but the cycle check comes first)
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, _, _, block0, _, region1, _) ← buildDeepTree
  return (block0.setParentWithCheck! ctx region1).isNone

-- Valid: freshBlock has no parent and region0 is not inside it → should succeed
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, _, region0, _, _, _, _) ← buildDeepTree
  let (ctx, freshBlock) ← BlockPtr.allocEmpty ctx
  return (freshBlock.setParentWithCheck! ctx region0).isSome

-- Existing parent: block0 already has parent region0 → should fail
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, _, _, block0, _, _, _) ← buildDeepTree
  let (ctx, freshRegion) ← RegionPtr.allocEmpty ctx
  return (block0.setParentWithCheck! ctx freshRegion).isNone

/-! ## Pre-existing cycle detection (fuel exhaustion) -/

/-- Build an IR with a cycle in parent pointers:
    op0 → region0 → block0 → op0 (cycle!)
    This is an invalid IR state, but containsBlock!/containsRegion! should
    handle it gracefully via fuel exhaustion. -/
private def buildCyclicTree :
    Option (IRContext OpCode × OperationPtr × RegionPtr × BlockPtr) := do
  let (ctx, op0) ← OperationPtr.allocEmpty (IRContext.empty OpCode) .builtin_module default
  let (ctx, region0) ← RegionPtr.allocEmpty ctx
  let (ctx, block0) ← BlockPtr.allocEmpty ctx
  let ctx := op0.pushRegion! ctx region0
  let ctx := region0.setParent! ctx op0
  let ctx := block0.setParent! ctx (some region0)
  -- Close the cycle: op0's parent → block0
  let ctx := op0.setParent! ctx (some block0)
  return (ctx, op0, region0, block0)

-- containsBlock! on a cyclic tree: walks up from block0, hits op0, then block0 again...
-- fuel exhaustion should conservatively return true
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, op0, _, block0) ← buildCyclicTree
  return op0.containsBlock! ctx block0

-- containsRegion! on a cyclic tree: walks up from region0, hits op0 → block0 → region0...
-- fuel exhaustion should conservatively return true
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, _, region0, block0) ← buildCyclicTree
  return block0.containsRegion! ctx region0

-- setParentWithCheck! rejects when the tree is already cyclic
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, _, _, block0) ← buildCyclicTree
  let (ctx, freshOp) ← OperationPtr.allocEmpty ctx .builtin_module default
  -- freshOp has no parent, block0 is in a cycle — containsBlock! will exhaust fuel
  -- and conservatively return true, rejecting the insertion
  return (freshOp.setParentWithCheck! ctx block0).isNone

-- Explicit fuel test: containsBlock! with fuel=0 always returns true (conservative)
/--
info: some true
-/
#guard_msgs in
#eval do
  let (ctx, op0, _, _) ← buildSimpleTree
  let (ctx, freshBlock) ← BlockPtr.allocEmpty ctx
  -- With fuel=0, even a non-cyclic case returns true conservatively
  return op0.containsBlock! ctx freshBlock (fuel := 0)
