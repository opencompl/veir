import Veir.Interfaces.FoldInterfaces

open Veir

/--
`hw` is the one dialect whose materializer no end-to-end test can reach: its
only operations are `constant`, `module`, and `output`, none of which folds.
The `comb` folds in `Test/Passes/Canonicalize/fold_constants.mlir` produce an
`hw.constant` through `Comb.materializeConstant`, not through this hook.
-/
private def testHWConstantMaterialization : String := Id.run do
  let i16 : TypeAttr := IntegerType.mk 16
  match (.hw .output : OpCode).materializeConstant (.int 16 (.val 9)) i16 with
  | some ⟨.hw .constant, props⟩ =>
    if props.value ≠ IntegerAttr.mk 9 (IntegerType.mk 16) then
      return "hw materialized the wrong constant"
    return "ok"
  | _ => return "hw did not materialize hw.constant"

/--
info: "ok"
-/
#guard_msgs in
#eval! testHWConstantMaterialization

/--
The dialects with no materializer decline rather than materializing something
from a neighbouring dialect. One representative per dialect; the dispatch in
`OpCode.materializeConstant` lists them all explicitly, so a newly added
dialect cannot silently join this set.
-/
private def testDialectsWithoutMaterializerDecline : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  let value : RuntimeValue := .int 32 (.val 3)
  let cases : Array (String × OpCode) := #[
    ("riscv_cf", .riscv_cf .branch), ("riscv_stack", .riscv_stack .alloca),
    ("rv64", .rv64 .get_register), ("cf", .cf .br), ("builtin", .builtin .module),
    ("func", .func .call), ("datapath", .datapath .compress),
    ("pdl", .pdl .operation), ("test", .test .test)
  ]
  for (name, opCode) in cases do
    if (opCode.materializeConstant value i32).isSome then
      return s!"{name} materialized a constant but has no materializer"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testDialectsWithoutMaterializerDecline

/-- A value whose width disagrees with the result type is never materialized. -/
private def testBitwidthMismatchIsRejected : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  match (.arith .addi : OpCode).materializeConstant (.int 16 (.val 7)) i32 with
  | none => return "ok"
  | some _ => return "arith materialized a constant of the wrong width"

/--
info: "ok"
-/
#guard_msgs in
#eval! testBitwidthMismatchIsRejected
