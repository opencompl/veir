import Veir.Input
import Veir.Rewriter.WfRewriter.ControlFlow
import Veir.Verifier

open Veir Veir.Input

namespace SuccessorOperandsTest

private def check (condition : Bool) (message : String) : Except String Unit :=
  if condition then pure () else throw message

/-- Compare actual use lists with an independent scan of all operation operands. -/
private def checkUses (ctx : WfIRContext OpCode) (values : Array ValuePtr) : Except String Unit := do
  for value in values do
    let mut expected : Array OpOperandPtr := #[]
    for op in ctx.raw.operations.keys do
      for use in op.getOpOperands! ctx.raw do
        if (use.get! ctx.raw).value == value then
          expected := expected.push use
    let mut seen : Array OpOperandPtr := #[]
    let mut current := value.getFirstUse! ctx.raw
    let mut back := OpOperandPtrPtr.valueFirstUse value
    for _ in [:expected.size + 1] do
      let some use := current | break
      check (!seen.contains use && expected.contains use) "unexpected or duplicate use"
      let operand := use.get! ctx.raw
      check (operand.back == back && operand.owner == use.op && operand.value == value)
        "broken use-def link"
      seen := seen.push use
      back := .operandNextUse use
      current := operand.nextUse
    check (current.isNone && seen.size == expected.size) "missing use or cyclic use list"

private def conditional := r#""func.func"() <{sym_name = "f", function_type = (FIXED_TYPES, TYPE, TYPE, TYPE) -> ()}> ({
^entry(FIXED_ARGS, %a : TYPE, %b : TYPE, %c : TYPE):
  "test.test"(%a, %b, %a, %c) : (TYPE, TYPE, TYPE, TYPE) -> ()
  "BRANCH"(FIXED_VALUES, %a, %b) [^left, ^right]
    <{operandSegmentSizes = array<WIDTH: SIZES>EXTRA}> {tag = "keep"}
    : (FIXED_TYPES, TYPE, TYPE) -> ()
^left(%x : TYPE):
  "test.test"(%x) : (TYPE) -> ()
  "func.return"() : () -> ()
^right(%y : TYPE):
  "test.test"(%y) : (TYPE) -> ()
  "func.return"() : () -> ()
}) : () -> ()"#

private def runConditional (name : String) (fixedCount : Nat := 1)
    (width : Nat := 32) (duplicateEdges : Bool := false) : Except String Unit := do
  let riscv := name.startsWith "riscv_cf."
  let fixedType := if riscv then "!riscv.reg" else "i1"
  let source := conditional.replace "FIXED_TYPES"
    (String.intercalate ", " (List.replicate fixedCount fixedType))
  let source := source.replace "FIXED_ARGS"
    (if fixedCount == 1 then s!"%lhs : {fixedType}" else s!"%lhs : {fixedType}, %rhs : {fixedType}")
  let source := source.replace "FIXED_VALUES" (if fixedCount == 1 then "%lhs" else "%lhs, %rhs")
  let source := source.replace "TYPE" (if riscv then "!riscv.reg" else "i32")
  let source := source.replace "BRANCH" name |>.replace "WIDTH" s!"i{width}"
  let source := source.replace "SIZES" (if fixedCount == 1 then "1, 1, 1" else "1, 1, 1, 1")
  let extra := if riscv then "" else ", branch_weights = array<i32: 7, 11>"
  let extra := if name == "llvm.cond_br" then
    extra ++ ", loop_annotation = #llvm.loop_annotation<mustProgress = true>" else extra
  let source := source.replace "EXTRA" extra
  let source := if duplicateEdges then source.replace "[^left, ^right]" "[^left, ^left]" else source
  let (ctx, top, _) ← parseSourceString source.toUTF8
  let entry := ((top.getRegion! ctx.raw 0).get! ctx.raw).firstBlock.get!
  let args := entry.getArguments! ctx.raw
  let fixed := args.extract 0 fixedCount
  let a := args[fixedCount]!
  let b := args[fixedCount + 1]!
  let c := args[fixedCount + 2]!
  let branch := (entry.get! ctx.raw).lastOp.get!
  let original := branch.get! ctx.raw
  let successors := branch.getSuccessors! ctx.raw
  let opType := branch.getOpType! ctx.raw
  let properties := branch.getProperties! ctx.raw opType
  let checkState := fun (ctx : WfIRContext OpCode) (left right : Array ValuePtr) => do
    check (branch.getOperands! ctx.raw == fixed ++ left ++ right) "wrong branch operands"
    let attrs := IsOpCode.toAttrDict opType (branch.getProperties! ctx.raw opType)
    let some (.denseArrayAttr sizes) := attrs["operandSegmentSizes".toUTF8]?
      | throw "missing segment sizes"
    check (sizes.values == Array.replicate fixedCount 1 ++ #[↑left.size, ↑right.size] &&
      sizes.elementType.bitwidth == width) "wrong segment sizes or element type"
    for (edge, expected) in #[(0, left), (1, right)] do
      check ((BranchOpInterface.getSuccessorOperands? branch edge ctx.raw).map (·.forwardedOperands)
        == some expected) "wrong successor query"
    checkUses ctx args

  let ctx ← WfRewriter.appendSuccessorOperands ctx branch 0 #[c, a]
  checkState ctx #[a, c, a] #[b]
  let ctx ← WfRewriter.appendSuccessorOperands ctx branch 1 #[c]
  checkState ctx #[a, c, a] #[b, c]
  let ctx ← WfRewriter.setSuccessorOperands ctx branch 0 #[]
  checkState ctx #[] #[b, c]
  let ctx ← WfRewriter.setSuccessorOperands ctx branch 1 #[c, b, a]
  checkState ctx #[] #[c, b, a]
  let ctx ← WfRewriter.setSuccessorOperands ctx branch 0 #[b]
  let ctx ← WfRewriter.setSuccessorOperands ctx branch 1 #[a]
  let ctx ← WfRewriter.appendSuccessorOperands ctx branch 0 #[]
  checkState ctx #[b] #[a]
  let updated := branch.get! ctx.raw
  check (updated.parent == original.parent && updated.prev == original.prev &&
    updated.next == original.next && updated.attrs == original.attrs &&
    branch.getSuccessors! ctx.raw == successors) "branch identity/metadata changed"
  check (decide (branch.getProperties! ctx.raw opType = properties)) "branch properties changed"
  ctx.verify top

  -- These are invalid API arguments, independent of the input IR's validity.
  check (WfRewriter.setSuccessorOperands ctx branch 2 #[a]).toOption.isNone "accepted invalid successor"
  check (WfRewriter.appendSuccessorOperands ctx ⟨1000000⟩ 0 #[a]).toOption.isNone "accepted invalid operation"
  let invalid : ValuePtr := .opResult ⟨⟨1000000⟩, 0⟩
  check (WfRewriter.appendSuccessorOperands ctx branch 0 #[invalid]).toOption.isNone "accepted invalid value"
  check (WfRewriter.setOperandRange ctx branch 100 0 #[]).toOption.isNone "accepted invalid operand range"

private def unconditional := r#""func.func"() <{sym_name = "f", function_type = (TYPE, TYPE) -> ()}> ({
^entry(%a : TYPE, %b : TYPE):
  "test.test"(%a, %b) : (TYPE, TYPE) -> ()
  "BRANCH"(%a) [^exit] : (TYPE) -> ()
^exit(%x : TYPE):
  "func.return"() : () -> ()
}) : () -> ()"#

private def runUnconditional (name : String) : Except String Unit := do
  let source := unconditional.replace "BRANCH" name
  let source := source.replace "TYPE" (if name == "riscv_cf.branch" then "!riscv.reg" else "i32")
  let source := if name == "llvm.br" then source.replace "[^exit]"
    "[^exit] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}>" else source
  let (ctx, top, _) ← parseSourceString source.toUTF8
  let entry := ((top.getRegion! ctx.raw 0).get! ctx.raw).firstBlock.get!
  let args := entry.getArguments! ctx.raw
  let branch := (entry.get! ctx.raw).lastOp.get!
  let opType := branch.getOpType! ctx.raw
  let properties := branch.getProperties! ctx.raw opType
  let ctx ← WfRewriter.setSuccessorOperands ctx branch 0 #[]
  check (branch.getOperands! ctx.raw == #[]) "failed to clear branch operands"
  checkUses ctx args
  let ctx ← WfRewriter.appendSuccessorOperands ctx branch 0 #[args[1]!, args[0]!, args[1]!]
  check (branch.getOperands! ctx.raw == #[args[1]!, args[0]!, args[1]!]) "failed to append branch operands"
  checkUses ctx args
  let ctx ← WfRewriter.setSuccessorOperands ctx branch 0 #[args[1]!]
  checkUses ctx args
  check (decide (branch.getProperties! ctx.raw opType = properties)) "branch properties changed"
  ctx.verify top

private def runUnsupported : Except String Unit := do
  let source := (unconditional.replace "TYPE" "i32").replace
    "\"BRANCH\"(%a) [^exit] : (i32) -> ()"
    "\"llvm.switch\"(%a, %b) [^exit] <{case_operand_segments = array<i32>, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i32, i32) -> ()"
  let (ctx, top, _) ← parseSourceString source.toUTF8
  let entry := ((top.getRegion! ctx.raw 0).get! ctx.raw).firstBlock.get!
  let branch := (entry.get! ctx.raw).lastOp.get!
  check (BranchOpInterface.getSuccessorOperands? branch 0 ctx.raw).isSome "read-only successor query failed"
  check (WfRewriter.appendSuccessorOperands ctx branch 0 #[]).toOption.isNone "accepted unsupported mutation"

/-- info: Except.ok () -/
#guard_msgs in
#eval do
  for name in #["cf.br", "llvm.br", "riscv_cf.branch"] do
    runUnconditional name
  for (name, fixedCount) in #[("cf.cond_br", 1), ("llvm.cond_br", 1),
      ("riscv_cf.beqz", 1), ("riscv_cf.bnez", 1), ("riscv_cf.beq", 2), ("riscv_cf.bne", 2),
      ("riscv_cf.blt", 2), ("riscv_cf.bge", 2), ("riscv_cf.bltu", 2), ("riscv_cf.bgeu", 2)] do
    for width in #[32, 64] do
      for duplicateEdges in #[false, true] do
        runConditional name fixedCount width duplicateEdges
  runUnsupported

end SuccessorOperandsTest
