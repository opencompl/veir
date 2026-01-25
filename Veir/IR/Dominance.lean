module

public import Veir.IR.Basic
public import Std.Data.HashSet.Basic
public import Std.Data.HashMap
open Std (HashMap)

namespace Veir
public section

structure DomTreeNodePtr where
  region: RegionPtr
  index: Nat
deriving Inhabited, Repr, DecidableEq, Hashable

structure DomTreeNode where
  -- The block in question
  block : BlockPtr
  -- Level in the tree
  level : Nat
  -- The immediate dominator of the block
  iDom : Option DomTreeNodePtr

  firstChild : Option DomTreeNodePtr -- Invariant: If firstChild is none, lastChild is none. If firstChild is some, lastChild is some.
  lastChild : Option DomTreeNodePtr -- Invariant: lastChild's sibling should always be none
  sibling : Option DomTreeNodePtr
deriving Inhabited

abbrev DomTree := Array DomTreeNode
abbrev DomContext := HashMap RegionPtr DomTree 

def DomTreeNode.new (block : BlockPtr) (iDom: Option DomTreeNodePtr) (domTree : DomTree) : DomTreeNode :=
{
  block := block
  level :=
  match iDom with
    | some domPtr => domTree[domPtr.index]!.level + 1
    | none => 0
  iDom := none
  firstChild := none
  lastChild := none
  sibling := none
}

def RegionPtr.getDomTree! (ptr: RegionPtr) (ctx: DomContext) : DomTree := ctx[ptr]!

def DomTreeNodePtr.getDomTree! (ptr: DomTreeNodePtr) (ctx: DomContext) : DomTree :=
  (ptr.region.getDomTree! ctx)

def DomTreeNodePtr.get! (ptr: DomTreeNodePtr) (ctx: DomContext) : DomTreeNode :=
  (ptr.getDomTree! ctx)[ptr.index]!

def DomTreeNodePtr.getBlock! (ptr: DomTreeNodePtr) (ctx: DomContext) : BlockPtr :=
  (ptr.get! ctx).block

def DomTreeNodePtr.getLevel! (ptr: DomTreeNodePtr) (ctx: DomContext) : Nat :=
  (ptr.get! ctx).level

def DomTreeNodePtr.getIDom! (ptr: DomTreeNodePtr) (ctx: DomContext) : Option DomTreeNodePtr :=
  (ptr.get! ctx).iDom

def DomTreeNodePtr.getFirstChild! (ptr: DomTreeNodePtr) (ctx: DomContext) : Option DomTreeNodePtr :=
  (ptr.get! ctx).firstChild

def DomTreeNodePtr.getLastChild! (ptr: DomTreeNodePtr) (ctx: DomContext) : Option DomTreeNodePtr :=
  (ptr.get! ctx).lastChild

def DomTreeNodePtr.getSibling! (ptr: DomTreeNodePtr) (ctx: DomContext) : Option DomTreeNodePtr :=
  (ptr.get! ctx).sibling

def DomTreeNodePtr.getLastChildSibling! (ptr: DomTreeNodePtr) (ctx: DomContext) : Option DomTreeNodePtr :=
  ((ptr.getLastChild! ctx).get!.getSibling! ctx)

def DomTreeNodePtr.isLeaf! (ptr: DomTreeNodePtr) (ctx: DomContext) : Bool :=
  (ptr.getFirstChild! ctx).isNone

def DomContext.updateNode! (ptr: DomTreeNodePtr) (f : DomTreeNode -> DomTreeNode) (ctx: DomContext) : DomContext :=
  let tree := (ptr.getDomTree! ctx)
  let tree' := tree.set! ptr.index (f (ptr.get! ctx))
  ctx.insert ptr.region tree'

def DomTreeNodePtr.addChild! (parent child: DomTreeNodePtr) (ctx: DomContext) : DomContext := 
  let parentNode := (parent.get! ctx) 

  if (child.getSibling! ctx).isSome then 
    panic! "cannot add child that already has siblings"
  else if !(parent.isLeaf! ctx) && 
          (parent.getLastChildSibling! ctx).isSome then 
    panic! "sibling of last child must be none" 
  else
    match parentNode.lastChild with
    | none => (ctx.updateNode! parent) (fun n => { n with firstChild := some child, lastChild := some child })
    | some last => 
      let ctx := (ctx.updateNode! last) (fun n => { n with sibling := some child })
      (ctx.updateNode! parent) (fun parentNode => { parentNode with lastChild := some child })

def DomTreeNodePtr.removeChild! (parent child: DomTreeNodePtr) (ctx: DomContext) : DomContext := Id.run do
  let childSibling := (child.getSibling! ctx)
  let parentLast := (parent.getLastChild! ctx)
  let parentFirst := (parent.getFirstChild! ctx)

  -- Check invariants
  if !(parent.isLeaf! ctx) && 
     (parent.getLastChildSibling! ctx).isSome then 
    panic! "sibling of last child must be none" 
  if childSibling.isNone ≠ (parentLast == some child) then
      panic! "parent's last child is not the same as the last sibling"  
  
  -- Special case: child being removed is first child in sibling list
  if parentFirst == child then
    if parentFirst == parentLast then
      (ctx.updateNode! parent) (fun n => { n with firstChild := none, lastChild := none })
    else
      let ctx := (ctx.updateNode! parent) (fun n => { n with firstChild := childSibling })
      (ctx.updateNode! child) (fun n => { n with sibling := none }) 
  else -- Iterate
    let prev := parentFirst
    match prev with
    | none => panic! "Not in immediate dominator children list!"
    | some prev => 
        let mut prev := prev
        let mut curr := (prev.getSibling! ctx) 
        while curr != child do
          match curr with
          | none => panic! "Not in immediate dominator children list!"
          | some sibling => prev := sibling; curr := (sibling.getSibling! ctx) 
        let ctx := (ctx.updateNode! prev) (fun n => { n with sibling := childSibling })
        if childSibling.isSome then
          (ctx.updateNode! child) (fun n => { n with sibling := none })
        else
          (ctx.updateNode! parent) (fun n => { n with lastChild := prev })


















private def regionBlocks (region: RegionPtr) (ctx: IRContext) : Array BlockPtr := Id.run do
  let first := (region.get! ctx).firstBlock.get!
  let last := (region.get! ctx).lastBlock.get!
  let mut blocks : Array BlockPtr := #[]
  let mut curr := first
  while curr != last do
    blocks := blocks.push curr
    curr := (curr.get! ctx).next.get!
  blocks.push curr

private def blockPredecessors (block: BlockPtr) (ctx: IRContext) : Array BlockPtr := Id.run do
  let mut preds : Array BlockPtr := #[]
  let mut use := (block.get! ctx).firstUse
  while use.isSome do
    let op := (use.get!.get! ctx).owner
    let pred := (op.get! ctx).parent.get!
    preds := preds.push pred
    use := (use.get!.get! ctx).nextUse
  return preds

private def blockSuccessors (block: BlockPtr) (ctx: IRContext) : Array BlockPtr := Id.run do
  let mut succs : Array BlockPtr := #[]
  match (block.get! ctx).lastOp with
  | none => return succs
  | some op =>
    for i in [0:op.getNumSuccessors! ctx] do
      succs := succs.push (op.getSuccessor! ctx i)
    return succs

private partial def visitPostOrder (b : BlockPtr) (ctx: IRContext) (visited : Std.HashSet BlockPtr) (post : Array BlockPtr) : Std.HashSet BlockPtr × Array BlockPtr := Id.run do
  let mut visited := visited
  let mut post := post
  if visited.contains b then
    return (visited, post) 
  visited := visited.insert b 
  for s in (blockSuccessors b ctx) do
    (visited, post) := visitPostOrder s ctx visited post
  post := post.push b
  return (visited, post)

private def reversePostOrder (entry: BlockPtr) (ctx: IRContext) : Array BlockPtr := 
  let (_, post) := visitPostOrder entry ctx {} #[] 
  post.reverse

private def reversePostOrderIndex (rpo : Array BlockPtr) : Std.HashMap BlockPtr Nat := Id.run do
  let mut index : Std.HashMap BlockPtr Nat := {}
  for i in [0:rpo.size] do
    index := index.insert rpo[i]! i 
  return index

private def intersect (block1 block2 : BlockPtr) (doms: Array (Option BlockPtr)) (idx: Std.HashMap BlockPtr Nat) : BlockPtr := Id.run do
  let mut finger1 := block1
  let mut finger2 := block2
  while finger1 != finger2 do
    while idx[finger1]! > idx[finger2]! do
      finger1 := doms[idx[finger1]!]!.get!
    while idx[finger2]! > idx[finger1]! do  
      finger2 := doms[idx[finger2]!]!.get!
  return finger1

def getDominanceInfo (region: RegionPtr) (ctx: IRContext) : Array BlockPtr := Id.run do 
  let blocks := regionBlocks region ctx 
  let rpo := reversePostOrder blocks[0]! ctx
  let idx := reversePostOrderIndex rpo
  let mut doms : Array (Option BlockPtr) := #[]
  for _ in [0:rpo.size] do
    doms := doms.push none
  doms := doms.set! idx[rpo[0]!]! (some rpo[0]!)
  let mut changed := true
  while changed do
    changed := false 
    for block in rpo do
      let mut newIdom := (blockPredecessors block ctx)[0]!
      for pred in rpo[1:] do
        if doms[idx[pred]!]!.isSome then
          newIdom := intersect pred newIdom doms idx 
      if doms[idx[block]!]! != newIdom then
        doms := doms.set! idx[block]! newIdom 
        changed := true
  return doms.map (fun b => b.get!)
 
