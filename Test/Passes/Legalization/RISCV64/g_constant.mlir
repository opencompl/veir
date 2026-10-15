// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %byte = "gmir.g_constant"() <{value = -1 : i16}> : () -> i16
    // CHECK:      %[[WIDE_BYTE:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}> : () -> i64
    // CHECK-NEXT: %[[NARROW_BYTE:.*]] = "gmir.g_trunc"(%[[WIDE_BYTE]]) : (i64) -> i16
    %non_byte = "gmir.g_constant"() <{value = -1 : i3}> : () -> i3
    // CHECK:      %[[WIDE_NON_BYTE:.*]] = "gmir.g_constant"() <{"value" = 7 : i64}> : () -> i64
    // CHECK-NEXT: %[[NARROW_NON_BYTE:.*]] = "gmir.g_trunc"(%[[WIDE_NON_BYTE]]) : (i64) -> i3
    "test.test"(%byte, %non_byte) : (i16, i3) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
