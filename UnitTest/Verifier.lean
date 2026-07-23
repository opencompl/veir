import Veir.Rewriter.WfRewriter.Basic
import Veir.Verifier

open Veir

/--
Build a well-formed IR context with one deliberately invalid CFG edge. The
source and target blocks belong to distinct regions, which cannot be expressed
through the MLIR parser because block references are region-scoped.

The resulting IR has this shape (the dashed arrow is the invalid successor):

```text
module
└─ moduleRegion
   └─ moduleBlock
      ├─ test.test op
      │  └─ sourceRegion
      │     └─ sourceBlock
      │        └─ cf.br ─ ─ ─ ┐
      └─ test.test op         │
         └─ targetRegion      │ invalid cross-region edge
            └─ targetBlock ◀─ ┘
```
-/
private def contextWithCrossRegionSuccessor : Except String (WfIRContext OpCode) := do
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let moduleRegion := moduleOp.getRegion! ctx.raw 0
  let moduleBlock := (moduleRegion.get! ctx.raw).firstBlock.get!

  let (ctx, sourceRegion) := WfRewriter.createRegion! ctx
  let (ctx, sourceBlock) :=
    WfRewriter.createBlock! ctx #[] (some (.atEnd sourceRegion))

  let (ctx, targetRegion) := WfRewriter.createRegion! ctx
  let (ctx, targetBlock) :=
    WfRewriter.createBlock! ctx #[] (some (.atEnd targetRegion))

  let (ctx, _) :=
      (WfRewriter.createOp! ctx (.test .test) #[] #[] #[] #[sourceRegion] ()
        (some (.atEnd moduleBlock))).get!
  let (ctx, _) :=
      (WfRewriter.createOp! ctx (.test .test) #[] #[] #[] #[targetRegion] ()
        (some (.atEnd moduleBlock))).get!

  let (ctx, _) :=
      (WfRewriter.createOp! ctx (.cf .br) #[] #[] #[targetBlock] #[] ()
        (some (.atEnd sourceBlock))).get!
  return ctx

private def verifyCrossRegionSuccessor : Except String Unit := do
  let ctx ← contextWithCrossRegionSuccessor
  ctx.verify

#guard verifyCrossRegionSuccessor =
  .error "Block successors must belong to the same region as their predecessor"
