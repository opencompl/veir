// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    // A `g_anyext` of a value that is not truncated is kept.
    %x_i8 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %ext = "gmir.g_anyext"(%x_i8) : (i8) -> i64
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i8) -> i64

    // Widening the `i8` `g_and` extends its operands with `g_anyext`, which cancels with their
    // `g_trunc` from `i64`.
    %x_i64 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %trunc = "gmir.g_trunc"(%x_i64) : (i64) -> i8
    %and = "gmir.g_and"(%trunc, %trunc) : (i8, i8) -> i8
    // CHECK-NEXT: %[[X_I64:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[AND:.*]] = "gmir.g_and"(%[[X_I64]], %[[X_I64]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[AND]]) : (i64) -> i8

    // A `g_anyext (g_trunc x)` narrower than `x` is a `g_trunc` of `x`.
    %narrower = "gmir.g_anyext"(%trunc) : (i8) -> i32
    // CHECK-NEXT: "gmir.g_trunc"(%[[X_I64]]) : (i64) -> i32

    // A `g_anyext (g_trunc x)` wider than `x` is a `g_anyext` of `x`.
    %x_i32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %trunc_i32 = "gmir.g_trunc"(%x_i32) : (i32) -> i8
    %wider = "gmir.g_anyext"(%trunc_i32) : (i8) -> i64
    // CHECK-NEXT: %[[X_I32:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
    // CHECK-NEXT: "gmir.g_anyext"(%[[X_I32]]) : (i32) -> i64

    // Once the `g_trunc`s cancel, the high bits of the wide `g_or` operands overlap, so it must not
    // keep `isDisjoint`.
    %a = "llvm.mlir.constant"() <{value = 257 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 258 : i64}> : () -> i64
    %a8 = "gmir.g_trunc"(%a) : (i64) -> i8
    %b8 = "gmir.g_trunc"(%b) : (i64) -> i8
    %or = "gmir.g_or"(%a8, %b8) <{isDisjoint}> : (i8, i8) -> i8
    // CHECK-NEXT: %[[A:.*]] = "llvm.mlir.constant"() <{"value" = 257 : i64}> : () -> i64
    // CHECK-NEXT: %[[B:.*]] = "llvm.mlir.constant"() <{"value" = 258 : i64}> : () -> i64
    // CHECK-NEXT: %[[OR:.*]] = "gmir.g_or"(%[[A]], %[[B]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[OR]]) : (i64) -> i8

    "test.test"(%ext, %and, %narrower, %wider, %or) : (i64, i8, i32, i64, i8) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
