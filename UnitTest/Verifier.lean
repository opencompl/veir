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
  let moduleBlock := (moduleRegion.getFirstBlock! ctx.raw).get!

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
  let block := (region.getFirstBlock! ctx.raw).get!
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
    let attr := IntegerAttr.mk value (IntegerType.signless width)
    let checks := #[
      ("arith.constant", verifyConstant (.arith .constant) (.int attr) attr.type),
      ("llvm.mlir.constant", verifyConstant (.llvm .mlir__constant) ⟨.integer attr⟩ attr.type),
      ("hw.constant", verifyConstant (.hw .constant) ⟨attr⟩ attr.type)
    ]
    for (name, result) in checks do
      let expected : Except String Unit := if valid then .ok ()
        else .error s!"{name}: value {value} is not normalized for i{width}"
      if result ≠ expected then return false
  return true

#guard testConstantNormalization

/-- A use in a detached region cannot reference a result inside the verified module. -/
private def outsideUserRejected : Except String Bool := do
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let body := ((moduleOp.getRegion! ctx.raw 0).getFirstBlock! ctx.raw).get!
  let ty : TypeAttr := IntegerType.signless 32
  let (ctx, region) := WfRewriter.createRegion! ctx
  let (ctx, entry) := WfRewriter.createBlock! ctx #[ty] (some (.atEnd region))
  let (ctx, _) := (WfRewriter.createOp! ctx Test.test #[] #[] #[] #[region] () (some (.atEnd body))).get!
  let arg : ValuePtr := .blockArgument (entry.getArgument 0)
  let (ctx, sum) := (WfRewriter.createOp! ctx Arith.addi #[ty] #[arg, arg] #[] #[] default
    (some (.atEnd entry))).get!
  ctx.verify moduleOp
  let (ctx, outside) := WfRewriter.createRegion! ctx
  let (ctx, block) := WfRewriter.createBlock! ctx #[] (some (.atEnd outside))
  let (ctx, _) := (WfRewriter.createOp! ctx Arith.addi #[ty] #[sum.getResult 0, arg] #[] #[] default
    (some (.atEnd block))).get!
  return ctx.verify moduleOp == .error "arith.addi: operand crosses the boundary of the verified module"

#guard outsideUserRejected = .ok true

/-- Definitions in a second tree cannot be operands of an operation in the module. -/
private def crossModuleOperandsRejected : Except String Bool := do
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let body := ((moduleOp.getRegion! ctx.raw 0).getFirstBlock! ctx.raw).get!
  let ty : TypeAttr := IntegerType.signless 32
  let (ctx, region) := WfRewriter.createRegion! ctx
  let (ctx, block) := WfRewriter.createBlock! ctx #[ty] (some (.atEnd region))
  let (ctx, otherModule) := (WfRewriter.createOp! ctx Builtin.module #[] #[] #[] #[region]
    (default : ModuleProperties) none).get!
  let (ctx, producer) := (WfRewriter.createOp! ctx Test.test #[ty] #[] #[] #[] ()
    (some (.atEnd block))).get!
  let (ctx, _) := (WfRewriter.createOp! ctx Test.test #[] #[producer.getResult 0] #[] #[] ()
    (some (.atEnd block))).get!
  ctx.verify moduleOp
  for value in #[ValuePtr.opResult (producer.getResult 0), .blockArgument (block.getArgument 0)] do
    let (invalid, _) := (WfRewriter.createOp! ctx Test.test #[] #[value] #[] #[] ()
      (some (.atEnd body))).get!
    if (invalid.verify moduleOp).isOk then return false
    let (externalUse, _) := (WfRewriter.createOp! ctx Test.test #[] #[value] #[] #[] () none).get!
    if externalUse.verify otherModule != .error "test.test: operand crosses the boundary of the verified module" then
      return false
  return true

#guard crossModuleOperandsRejected = .ok true
