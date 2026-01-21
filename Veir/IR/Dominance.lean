module

public import Veir.IR.Basic
public import Std.Data.HashSet.Basic
public import Std.Data.HashMap.Basic

namespace Veir
public section

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
 
