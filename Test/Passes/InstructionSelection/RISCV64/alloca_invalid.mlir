// RUN: veir-opt %s -p=isel-riscv64 > %t
// RUN: filecheck %s --input-file=%t
// RUN: filecheck %s --input-file=%t --check-prefix=ABSENT

// ABSENT: "builtin.module"
// ABSENT-NOT: riscv_stack.alloca

// Unsupported allocations remain LLVM operations. Keep their results live so
// the greedy driver's ordinary dead-code elimination does not erase them.
"builtin.module"() ({
  "func.func"() <{sym_name = "unsupported", function_type = (i64) -> ()}> ({
  ^entry(%n: i64):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %large = "llvm.mlir.constant"() <{value = 2305843009213693952 : i64}> : () -> i64
    %wide = "llvm.mlir.constant"() <{value = 18446744073709551616 : i128}> : () -> i128

    %dynamic = "llvm.alloca"(%n) <{elem_type = i64}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 0 : i64, "elem_type" = i64}>
    %special = "llvm.alloca"(%one) <{elem_type = i8, inalloca}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 0 : i64, "elem_type" = i8, inalloca}>
    %layout = "llvm.alloca"(%one) <{elem_type = !llvm.struct<(i32, i64)>}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 0 : i64, "elem_type" = !llvm.struct<(i32, i64)>}>

    // The byte size must fit 64 bits without wrapping, even for a wide count.
    %overflow = "llvm.alloca"(%large) <{elem_type = i64}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 0 : i64, "elem_type" = i64}>
    %wide_count = "llvm.alloca"(%wide) <{elem_type = i8}> : (i128) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 0 : i64, "elem_type" = i8}>

    // The LLVM verifier currently accepts these, but they cannot become valid
    // fixed stack objects with the requested alignment/result type.
    %bad_align = "llvm.alloca"(%one) <{elem_type = i8, alignment = 3 : i64}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 3 : i64, "elem_type" = i8}>
    %negative_align = "llvm.alloca"(%one) <{elem_type = i8, alignment = -8 : i64}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = -8 : i64, "elem_type" = i8}>
    %wide_align = "llvm.alloca"(%one) <{elem_type = i8, alignment = 18446744073709551616 : i64}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 18446744073709551616 : i64, "elem_type" = i8}>
    %not_pointer = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> i64
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 0 : i64, "elem_type" = i8}> : (i64) -> i64
    "test.test"(%dynamic, %special, %layout, %overflow, %wide_count, %bad_align, %negative_align, %wide_align, %not_pointer) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"()[^later] : () -> ()
  ^later:
    // A constant-count alloca outside the entry block is still dynamic.
    %non_entry = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 0 : i64, "elem_type" = i8}>
    "test.test"(%non_entry) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // A region's first block is insufficient: it must belong to a function.
  "test.test"() ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %outside = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
    // CHECK: "llvm.alloca"({{.*}}) <{"alignment" = 0 : i64, "elem_type" = i8}>
    "test.test"(%outside) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()
