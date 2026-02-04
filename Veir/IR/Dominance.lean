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
  -- The immediate dominator of the block
  iDom : Option DomTreeNodePtr

  firstChild : Option DomTreeNodePtr -- Invariant: If firstChild is none, lastChild is none. If firstChild is some, lastChild is some.
  lastChild : Option DomTreeNodePtr -- Invariant: lastChild's sibling should always be none
  sibling : Option DomTreeNodePtr
deriving Inhabited

abbrev DomTree := Array DomTreeNode
abbrev DomContext := HashMap RegionPtr DomTree 

def DomTreeNode.new (block : BlockPtr) (iDom: Option DomTreeNodePtr) : DomTreeNode :=
{
  block := block
  iDom := iDom 
  firstChild := none
  lastChild := none
  sibling := none
}

def RegionPtr.getDomTree! (ptr: RegionPtr) (ctx: DomContext) : DomTree := ctx[ptr]!

def RegionPtr.newDomTreeNode! (ptr: RegionPtr) (block : BlockPtr) (ctx: DomContext) : DomContext := 
  let tree := (ptr.getDomTree! ctx).push (DomTreeNode.new block none)
  ctx.insert ptr tree

def RegionPtr.getDomTreeSize! (ptr: RegionPtr) (ctx: DomContext) : Nat :=
  let tree := (ptr.getDomTree! ctx)
  tree.size

def DomTreeNodePtr.getDomTree! (ptr: DomTreeNodePtr) (ctx: DomContext) : DomTree :=
  (ptr.region.getDomTree! ctx)

def DomTreeNodePtr.get! (ptr: DomTreeNodePtr) (ctx: DomContext) : DomTreeNode :=
  (ptr.getDomTree! ctx)[ptr.index]!

def DomTreeNodePtr.getBlock! (ptr: DomTreeNodePtr) (ctx: DomContext) : BlockPtr :=
  (ptr.get! ctx).block

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

  def DomTreeNodePtr.setIDom! (ptr newIDom: DomTreeNodePtr) (ctx: DomContext) : DomContext := Id.run do
    match (ptr.getIDom! ctx) with
    | none => panic! "No immediate dominator"
    | some iDom =>
      if iDom == newIDom then 
        return ctx
      else
        let ctx := (iDom.removeChild! ptr ctx)
        (newIDom.addChild! ptr ctx)

-- Uses the Cooper Harvey Kennedy algorithm
def RegionPtr.computeDomTree! (ptr: RegionPtr) (domCtx: DomContext) (irCtx : IRContext) : DomContext := Id.run do 
  let intersect (block1: BlockPtr) (block2: BlockPtr) (idx: HashMap BlockPtr DomTreeNodePtr) : BlockPtr := Id.run do 
    let mut finger1 := idx[block1]!
    let mut finger2 := idx[block2]!
    while finger1 != finger2 do
      while finger1.index < finger2.index do
        finger1 := (finger1.getIDom! domCtx).get! 
      while finger2.index < finger1.index do  
        finger2 := (finger2.getIDom! domCtx).get! 
    return (finger1.getBlock! domCtx)
    
  -- Postorder traversal of blocks, insert into DomTree (which is just an array!) 
  let mut postOrderIndex : HashMap BlockPtr DomTreeNodePtr := {}
  let mut domCtx := domCtx
  domCtx := domCtx.insert ptr #[]  
  match (ptr.get! irCtx).firstBlock with
  | none => return domCtx
  | some entry =>
    let mut worklist : Array (Option BlockPtr × Bool) := #[(entry, false)]
    while not worklist.isEmpty do
      let (block, visited) := worklist.back!
      worklist := worklist.pop 
      match block with
      | none => continue
      | some block =>
        if visited then 
          postOrderIndex := postOrderIndex.insert block { region := ptr, index := (ptr.getDomTreeSize! domCtx) }
          domCtx := ptr.newDomTreeNode! block domCtx 
        else
          worklist := worklist.push (block, true) 
          let op := (block.get! irCtx).lastOp.get!
          for childIdx in [0:op.getNumSuccessors! irCtx] do
            worklist := worklist.push ((op.getSuccessor! irCtx childIdx), false)
   
  -- Iterate backwards through the DomTree (reverse postorder traversal)
  let mut changed := true
  while changed do
    let domTree := (ptr.getDomTree! domCtx)
    changed := false
    for node in domTree.reverse do
      let newIDom := (node.block.get! irCtx).firstUse
      let mut pred := (newIDom.get!.get! irCtx).nextUse
      let mut newIDom := ((newIDom.get!.get! irCtx).owner.get! irCtx).parent.get!
      while pred.isSome do
        let predBlock := ((pred.get!.get! irCtx).owner.get! irCtx).parent.get! 
        if domTree[postOrderIndex[predBlock]!.index]!.iDom.isSome then
          newIDom := intersect predBlock newIDom postOrderIndex 
        pred := (pred.get!.get! irCtx).nextUse 
      let nodePtr := postOrderIndex[node.block]!
      let newIDomPtr := postOrderIndex[newIDom]!
      if (nodePtr.getIDom! domCtx) != newIDomPtr then
        domCtx := DomContext.updateNode! nodePtr (fun n => { n with iDom := some newIDomPtr }) domCtx 
        domCtx := newIDomPtr.addChild! nodePtr domCtx
        changed := true
  domCtx
