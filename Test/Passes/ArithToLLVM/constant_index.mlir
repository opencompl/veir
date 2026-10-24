// RUN: veir-opt %s --print-op-generic -p=arith-to-llvm | filecheck %s

// Lowering an index constant needs an index -> i64 conversion, so the pass
// leaves it alone.
"builtin.module"() ({
  "func.func"() <{sym_name = "constants", function_type = () -> (index, i32)}> ({
    %idx = "arith.constant"() <{value = 4 : index}> : () -> index
    %int = "arith.constant"() <{value = 4 : i32}> : () -> i32
    "func.return"(%idx, %int) : (index, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "arith.constant"() <{"value" = 4 : index}> : () -> index
// CHECK: "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
