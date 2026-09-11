// RUN: veir-interpret %s | filecheck %s

// A switch with no cases at all is an unconditional branch to its default.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %v = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
      %d = "llvm.mlir.constant"() <{"value" = 42 : i32}> : () -> i32
      "llvm.switch"(%v, %d) [^dflt]
        <{"case_operand_segments" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 0>}> : (i32, i32) -> ()
    ^dflt(%x : i32):
      "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32]
