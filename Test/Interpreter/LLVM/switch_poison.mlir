// RUN: veir-interpret %s | filecheck %s

// Switching on a poison value is undefined behaviour, as branching on a poison
// condition is for `llvm.cond_br`.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %poison = "llvm.mlir.poison"() : () -> i32
      %d = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
      %a = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
      "llvm.switch"(%poison, %d, %a) [^dflt, ^c0]
        <{"case_operand_segments" = array<i32: 1>, "case_values" = dense<[13]> : vector<1xi32>,
          "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i32, i32, i32) -> ()
    ^dflt(%x : i32):
      "llvm.return"(%x) : (i32) -> ()
    ^c0(%y : i32):
      "llvm.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
