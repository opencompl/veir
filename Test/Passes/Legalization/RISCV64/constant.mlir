// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    // `i64` is legal.
    %x_i64 = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    // CHECK:      "gmir.g_constant"() <{"value" = -1 : i64}> : () -> i64

    // Constants of a whole number of bytes are sign-extended.
    %x_i32 = "gmir.g_constant"() <{value = -2 : i32}> : () -> i32
    // CHECK:      %[[WIDE:.*]] = "gmir.g_constant"() <{"value" = -2 : i64}> : () -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[WIDE]]) : (i64) -> i32

    // Other constants are zero-extended.
    %x_i3 = "gmir.g_constant"() <{value = -1 : i3}> : () -> i3
    // CHECK:      %[[WIDE:.*]] = "gmir.g_constant"() <{"value" = 7 : i64}> : () -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[WIDE]]) : (i64) -> i3

    "test.test"(%x_i64, %x_i32, %x_i3) : (i64, i32, i3) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
