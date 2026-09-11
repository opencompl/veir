// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p=isel-riscv64 > %t.partial
// RUN: veir-interpret %t.partial | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p=riscv > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --input-file=%t --implicit-check-not=llvm.alloca --implicit-check-not=builtin.unrealized_conversion_cast

// i24 occupies four bytes per element. Keep a second object live and store it
// first, so omitting padding would let the subsequent array store corrupt it.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %array = "llvm.alloca"(%three) <{elem_type = i24, alignment = 16 : i64}> : (i64) -> !llvm.ptr
    // CHECK: %[[ARRAY:.*]] = "riscv_stack.alloca"() <{"alignment" = 16 : i64, "size" = 12 : i64}>
    %slot = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    // CHECK: %[[SLOT:.*]] = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}>
    %value = "llvm.mlir.constant"() <{value = 170 : i64}> : () -> i64
    "llvm.store"(%value, %slot) : (i64, !llvm.ptr) -> ()
    // CHECK: "riscv.sd"({{.*}}, %[[SLOT]])
    %last = "llvm.getelementptr"(%array, %one) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %zero32 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.store"(%zero32, %last) : (i32, !llvm.ptr) -> ()
    // CHECK: "riscv.sw"({{.*}}, %[[ARRAY]]) <{"value" = 8 : i64}>
    %out = "llvm.load"(%slot) : (!llvm.ptr) -> i64
    // CHECK: "riscv.ld"(%[[SLOT]])
    "llvm.return"(%out) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x00000000000000aa#64]
