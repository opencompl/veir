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

private def verifyConstant (opType : OpCode) (props : propertiesOf opType)
    (type : IntegerType) : Except String Unit := do
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let region := moduleOp.getRegion! ctx.raw 0
  let block := (region.get! ctx.raw).firstBlock.get!
  let (ctx, _) :=
    (WfRewriter.createOp! ctx opType #[type] #[] #[] #[] props
      (some (.atEnd block))).get!
  ctx.verify moduleOp

/--
Construct attributes directly: the parser normalizes or rejects these spellings
before verification. Each dialect must reject noncanonical values and accept
the normalized boundary values.
-/
private def testConstantNormalization : Bool := Id.run do
  for (width, value, valid) in ([
      (1, -1, false), (1, 2, false), (8, 128, false),
      (8, -129, false), (8, 256, false),
      (1, 0, true), (1, 1, true), (8, -128, true), (8, 127, true)
    ] : List (Nat × Int × Bool)) do
    let attr := IntegerAttr.mk value (IntegerType.mk width)
    let checks := #[
      ("arith.constant", verifyConstant (.arith .constant) ⟨attr⟩ attr.type),
      ("llvm.mlir.constant", verifyConstant (.llvm .mlir__constant) ⟨.integer attr⟩ attr.type),
      ("hw.constant", verifyConstant (.hw .constant) ⟨attr⟩ attr.type)
    ]
    for (name, result) in checks do
      let expected : Except String Unit := if valid then .ok ()
        else .error s!"{name}: value {value} is not normalized for i{width}"
      if result ≠ expected then return false
  return true

#guard testConstantNormalization
