// RUN: veir-opt %s --print-op-generic -p=arith-to-llvm | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "constants", function_type = () -> (i8, i8, i8, i1)}> ({
    %unsigned = "arith.constant"() <{value = 200 : i8}> : () -> i8
    %allOnes = "arith.constant"() <{value = 255 : i8}> : () -> i8
    // Already signed: must survive unchanged.
    %signed = "arith.constant"() <{value = -128 : i8}> : () -> i8
    %bit = "arith.constant"() <{value = 1 : i1}> : () -> i1
    "func.return"(%unsigned, %allOnes, %signed, %bit) : (i8, i8, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.constant"() <{"value" = -56 : i8}> : () -> i8
// CHECK: "llvm.mlir.constant"() <{"value" = -1 : i8}> : () -> i8
// CHECK: "llvm.mlir.constant"() <{"value" = -128 : i8}> : () -> i8
// CHECK: "llvm.mlir.constant"() <{"value" = true}> : () -> i1
