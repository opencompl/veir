// RUN: veir-interpret %s | filecheck %s

// No case value matches, so the default destination is taken -- with the
// default's own operand segment, which sits before every case's.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %v = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
      %d = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
      %a = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
      %b = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
      "llvm.switch"(%v, %d, %a, %b) [^dflt, ^c0, ^c1]
        <{"case_operand_segments" = array<i32: 1, 1>, "case_values" = dense<[13, 35]> : vector<2xi32>,
          "operandSegmentSizes" = array<i32: 1, 1, 2>}> : (i32, i32, i32, i32) -> ()
    ^dflt(%x : i32):
      "llvm.return"(%x) : (i32) -> ()
    ^c0(%y : i32):
      "llvm.return"(%y) : (i32) -> ()
    ^c1(%z : i32):
      "llvm.return"(%z) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32]
