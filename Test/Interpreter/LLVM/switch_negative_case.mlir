// RUN: veir-interpret %s | filecheck %s

// Case values are compared as bit patterns of the switched value's width, so a
// negative case value matches the wrapped constant rather than nothing.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %v = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
      %d = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
      %a = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
      "llvm.switch"(%v, %d, %a) [^dflt, ^c0]
        <{"case_operand_segments" = array<i32: 1>, "case_values" = dense<[-1]> : vector<1xi32>,
          "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i32, i32, i32) -> ()
    ^dflt(%x : i32):
      "llvm.return"(%x) : (i32) -> ()
    ^c0(%y : i32):
      "llvm.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000002#32]
