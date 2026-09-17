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
private def contextWithCrossRegionSuccessor :
    Except String (WfIRContext OpCode × OperationPtr) := do
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
      (WfRewriter.createOp! ctx Test.test #[] #[] #[] #[sourceRegion] ()
        (some (.atEnd moduleBlock))).get!
  let (ctx, _) :=
      (WfRewriter.createOp! ctx Test.test #[] #[] #[] #[targetRegion] ()
        (some (.atEnd moduleBlock))).get!

  let (ctx, _) :=
      (WfRewriter.createOp! ctx Cf.br #[] #[] #[targetBlock] #[] ()
        (some (.atEnd sourceBlock))).get!
  return (ctx, moduleOp)

private def verifyCrossRegionSuccessor : Except String Unit := do
  let (ctx, moduleOp) ← contextWithCrossRegionSuccessor
  ctx.verify moduleOp

#guard verifyCrossRegionSuccessor =
  .error "Block successors must belong to the same region as their predecessor"

/-- Construct constants without parsing, so these checks also catch invalid IR
created by a rewrite. Keep the raw literal rather than using `ofInt`. -/
private def verifyIntegerConstant (value : Int) (attrWidth resultWidth : Nat) : Except String Unit := do
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let region := moduleOp.getRegion! ctx.raw 0
  let block := (region.get! ctx.raw).firstBlock.get!
  let properties := LLVMConstantProperties.mk (.integer ⟨value, ⟨attrWidth⟩⟩)
  let (ctx, _) := (WfRewriter.createOp! ctx Llvm.mlir__constant
    #[IntegerType.mk resultWidth] #[] #[] #[] properties (some (.atEnd block))).get!
  ctx.verify moduleOp

#guard verifyIntegerConstant 256 8 8 =
  .error "llvm.mlir.constant: integer constant out of range for attribute"
#guard verifyIntegerConstant (-129) 8 8 =
  .error "llvm.mlir.constant: integer constant out of range for attribute"
#guard verifyIntegerConstant 2 1 1 =
  .error "llvm.mlir.constant: integer constant out of range for attribute"
#guard verifyIntegerConstant 1 32 8 =
  .error "llvm.mlir.constant: integer attribute and result types must match"
#guard verifyIntegerConstant (-1) 1 8 =
  .error "llvm.mlir.constant: integer attribute and result types must match"
