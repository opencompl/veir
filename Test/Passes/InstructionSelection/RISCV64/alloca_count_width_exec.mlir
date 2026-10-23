// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p=riscv > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --input-file=%t
// RUN: filecheck %s --input-file=%t --check-prefix=ABSENT

// ABSENT: "builtin.module"
// ABSENT-NOT: llvm.alloca

// Static allocations with counts narrower and wider than a register. The
// counts are read when translating to gMIR, so they never need legalization:
// widening the narrow ones would hide them behind a `gmir.g_trunc`, and the
// `i128` one has no legalization rule at all.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %two_i8 = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %two_i32 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %two_i128 = "llvm.mlir.constant"() <{value = 2 : i128}> : () -> i128
    %a = "llvm.alloca"(%two_i8) <{elem_type = i64}> : (i8) -> !llvm.ptr
    // CHECK: %[[A:.*]] = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 16 : i64}>
    %b = "llvm.alloca"(%two_i32) <{elem_type = i32}> : (i32) -> !llvm.ptr
    // CHECK: %[[B:.*]] = "riscv_stack.alloca"() <{"alignment" = 4 : i64, "size" = 8 : i64}>
    %c = "llvm.alloca"(%two_i128) <{elem_type = i16}> : (i128) -> !llvm.ptr
    // CHECK: %[[C:.*]] = "riscv_stack.alloca"() <{"alignment" = 2 : i64, "size" = 4 : i64}>
    %x = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %y = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %z = "llvm.mlir.constant"() <{value = 0 : i16}> : () -> i16
    "llvm.store"(%x, %a) : (i64, !llvm.ptr) -> ()
    "llvm.store"(%y, %b) : (i32, !llvm.ptr) -> ()
    "llvm.store"(%z, %c) : (i16, !llvm.ptr) -> ()
    %la = "llvm.load"(%a) : (!llvm.ptr) -> i64
    %lb32 = "llvm.load"(%b) : (!llvm.ptr) -> i32
    %lc16 = "llvm.load"(%c) : (!llvm.ptr) -> i16
    %lb = "llvm.zext"(%lb32) : (i32) -> i64
    %lc = "llvm.zext"(%lc16) : (i16) -> i64
    %ab = "llvm.add"(%la, %lb) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %sum = "llvm.add"(%ab, %lc) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.return"(%sum) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x000000000000002a#64]
