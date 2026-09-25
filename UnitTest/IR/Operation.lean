import Veir.Input

open Veir
open Veir.Input

/- The snippets only exercise IR accessors, so they need not verify. -/

private def noRegions :=
  parseSourceString! r#""arith.muli"() : () -> ()"#.toUTF8 (verifyAfterParse := false)
#guard noRegions.2.getNumRegions! noRegions.1.raw == 0

private def oneRegion := parseSourceString! r#""arith.addi"() ({
  "arith.muli"() : () -> ()
}) : () -> ()"#.toUTF8 (verifyAfterParse := false)
#guard oneRegion.2.getNumRegions! oneRegion.1.raw == 1

private def twoRegions := parseSourceString! r#""arith.addi"() ({
  "arith.muli"() : () -> ()
}, {
  "arith.muli"() : () -> ()
}) : () -> ()"#.toUTF8 (verifyAfterParse := false)
#guard twoRegions.2.getNumRegions! twoRegions.1.raw == 2
#guard (twoRegions.2.getRegions! twoRegions.1.raw).size ==
  twoRegions.2.getNumRegions! twoRegions.1.raw
#guard (twoRegions.2.getRegions! twoRegions.1.raw)[0]! == twoRegions.2.getRegion! twoRegions.1.raw 0
#guard (twoRegions.2.getRegions! twoRegions.1.raw)[1]! == twoRegions.2.getRegion! twoRegions.1.raw 1
private def flattenOps (top : OperationPtr) (ctx : IRContext OpCode) :
    Array OperationPtr := Id.run do
  let mut ops := #[]
  for region in (top.get! ctx).regions do
    let region := region.get! ctx
    let mut currentBlock := region.firstBlock
    while let some block := currentBlock do
      let mut currentOp := (block.get! ctx).firstOp
      while let some op := currentOp do
        ops := ops.push op
        currentOp := (op.get! ctx).next
      currentBlock := (block.get! ctx).next
  ops

private def parsed := parseSourceString! r#""builtin.module"() ({
  %a = "test.test"() : () -> i32
  %b = "test.test"() : () -> i32
  %c = "arith.muli"(%a, %b) : (i32, i32) -> i32
}) : () -> ()"#.toUTF8 (verifyAfterParse := false)

private def ctx := parsed.1.raw
private def ops := flattenOps parsed.2 ctx

#guard ops[0]!.getNumOperands! ctx == 0
#guard (ops[0]!.getOpOperands! ctx).size == 0

#guard ops[2]!.getNumOperands! ctx == 2
#guard (ops[2]!.getOpOperands! ctx).size == ops[2]!.getNumOperands! ctx
#guard (ops[2]!.getOpOperands! ctx)[0]! == ops[2]!.getOpOperand 0
#guard (ops[2]!.getOpOperands! ctx)[1]! == ops[2]!.getOpOperand 1

#guard (ops[2]!.getOpOperands! ctx)[0]!.op == ops[2]!
#guard (ops[2]!.getOpOperands! ctx)[0]!.index == 0
#guard (ops[2]!.getOpOperands! ctx)[1]!.index == 1

#guard ops[2]!.getOperand! ctx 0 == (ops[0]!.getResult 0 : ValuePtr)
#guard ops[2]!.getOperand! ctx 1 == (ops[1]!.getResult 0 : ValuePtr)
