// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %0 = "llvm.mlir.constant"() <{"value" = 13 : i8}> : () -> i8
      %1 = "builtin.unrealized_conversion_cast"(%0) : (i8) -> !riscv.reg
      %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
      // CHECK:          %{{.*}} = "llvm.mlir.constant"() <{"value" = 13 : i8}> : () -> i8
      // CHECK-NEXT:     %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> !riscv.reg
      // CHECK-NEXT:     %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

