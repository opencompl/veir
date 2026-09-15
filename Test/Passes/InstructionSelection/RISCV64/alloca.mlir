// RUN: veir-opt %s -p=isel-riscv64 > %t
// RUN: filecheck %s --input-file=%t
// RUN: filecheck %s --input-file=%t --check-prefix=ABSENT

// ABSENT: "builtin.module"
// ABSENT-NOT: llvm.alloca
// ABSENT-NOT: llvm.mlir.constant

"builtin.module"() ({
  "func.func"() <{sym_name = "layout", function_type = () -> ()}> ({
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i128}> : () -> i128
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32

    // Missing/zero alignment uses ABI alignment; explicit alignment is preserved.
    %default = "llvm.alloca"(%three) <{elem_type = i32}> : (i64) -> !llvm.ptr
    // CHECK: %[[DEFAULT:.*]] = "riscv_stack.alloca"() <{"alignment" = 4 : i64, "size" = 12 : i64}> : () -> !riscv.reg
    // CHECK-NEXT: %[[PTR:.*]] = "builtin.unrealized_conversion_cast"(%[[DEFAULT]]) : (!riscv.reg) -> !llvm.ptr
    %explicit = "llvm.alloca"(%three) <{elem_type = i32, alignment = 32 : i64}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 32 : i64, "size" = 12 : i64}>
    %small_align = "llvm.alloca"(%three) <{elem_type = i64, alignment = 1 : i64}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 1 : i64, "size" = 24 : i64}>

    // Allocation stride includes a whole byte for i1 and tail padding for i24.
    %narrow = "llvm.alloca"(%three) <{elem_type = i1}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 1 : i64, "size" = 3 : i64}>
    %padded = "llvm.alloca"(%three) <{elem_type = i24, alignment = 0 : i64}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 4 : i64, "size" = 12 : i64}>
    %array = "llvm.alloca"(%two) <{elem_type = !llvm.array<3 x i24>}> : (i128) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 4 : i64, "size" = 24 : i64}>

    // Both zero counts and zero-sized element types produce zero-sized objects.
    %zero_count = "llvm.alloca"(%zero) <{elem_type = i64}> : (i32) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 0 : i64}>
    %zero_type = "llvm.alloca"(%three) <{elem_type = !llvm.array<0 x i64>}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 0 : i64}>

    // CHECK: "test.test"(%[[PTR]]) : (!llvm.ptr) -> ()
    "test.test"(%default) : (!llvm.ptr) -> ()
    "test.test"(%explicit, %small_align, %narrow, %padded, %array, %zero_count, %zero_type) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // llvm.func entry blocks are eligible too. Interpret count constants at their
  // SSA width, including the special zero-extension rule for i1 attributes.
  "llvm.func"() <{sym_name = "count_bits", function_type = !llvm.func<void ()>}> ({
    %negative = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %boolean = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %extended = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i16
    %truncated = "llvm.mlir.constant"() <{value = 257 : i16}> : () -> i8
    %a = "llvm.alloca"(%negative) <{elem_type = i8}> : (i8) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 1 : i64, "size" = 255 : i64}>
    %b = "llvm.alloca"(%boolean) <{elem_type = i8}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 1 : i64, "size" = 1 : i64}>
    %c = "llvm.alloca"(%extended) <{elem_type = i8}> : (i16) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 1 : i64, "size" = 65535 : i64}>
    %d = "llvm.alloca"(%truncated) <{elem_type = i8}> : (i8) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 1 : i64, "size" = 1 : i64}>
    "test.test"(%a, %b, %c, %d) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()

  // Any supported constant-like integer count is sufficient.
  "func.func"() <{sym_name = "constant_like", function_type = () -> ()}> ({
    %two = "arith.constant"() <{value = 2 : i32}> : () -> i32
    %zero = "llvm.mlir.zero"() : () -> i64
    %a = "llvm.alloca"(%two) <{elem_type = i64}> : (i32) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 16 : i64}>
    %b = "llvm.alloca"(%zero) <{elem_type = i64}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 0 : i64}>
    "test.test"(%a, %b) : (!llvm.ptr, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
