// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    %0 = "arith.constant"() <{value = 0 : index}> : () -> index
    %1 = "arith.constant"() <{value = 42 : index}> : () -> index
    %2 = "arith.constant"() <{value = -1 : index}> : () -> index
    %3 = "arith.constant"() <{value = 9223372036854775807 : index}> : () -> index
    %4 = "arith.constant"() <{value = -9223372036854775808 : index}> : () -> index
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "arith.constant"() <{"value" = 0 : index}> : () -> index
// CHECK: "arith.constant"() <{"value" = 42 : index}> : () -> index
// CHECK: "arith.constant"() <{"value" = -1 : index}> : () -> index
// CHECK: "arith.constant"() <{"value" = 9223372036854775807 : index}> : () -> index
// CHECK: "arith.constant"() <{"value" = -9223372036854775808 : index}> : () -> index
