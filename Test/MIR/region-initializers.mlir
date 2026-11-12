// RUN: veir-opt %s -p=riscv > %t
// RUN: filecheck %s --input-file=%t --check-prefix=IR
// RUN: veir2mir %t | filecheck %s

// XFAIL: *
// Needs `reconcileRegToPtr`, commented out of the pass as unproven.

// Lowering applies to functions only: initializer regions stay LLVM operations,
// so `veir2mir` can turn them back into constants of the stub IR module.

"builtin.module"() ({
  "llvm.mlir.global"() <{global_type = i32, linkage = #llvm.linkage<internal>, sym_name = "by_region"}> ({
    %c = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.return"(%c) : (i32) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "points_to"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @by_region}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "null_ptr"}> ({
    %z = "llvm.mlir.zero"() : () -> !llvm.ptr
    "llvm.return"(%z) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = i64, linkage = #llvm.linkage<external>, sym_name = "zero_int"}> ({
    %z = "llvm.mlir.zero"() : () -> i64
    "llvm.return"(%z) : (i64) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "function_ptr"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @external_function}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, sym_name = "external_function"}> ({}) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "read"}> ({
    %g = "llvm.mlir.addressof"() <{global_name = @zero_int}> : () -> !llvm.ptr
    %v = "llvm.load"(%g) : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// IR:      "sym_name" = "by_region"
// IR-NOT:  riscv
// IR:      "llvm.mlir.constant"
// IR-NOT:  riscv
// IR:      "llvm.return"
// IR-NOT:  riscv
// IR:      "sym_name" = "points_to"
// IR-NOT:  riscv
// IR:      "llvm.mlir.addressof"
// IR-NOT:  riscv
// IR:      "llvm.return"
// IR-NOT:  riscv
// IR:      "sym_name" = "null_ptr"
// IR-NOT:  riscv
// IR:      "llvm.mlir.zero"
// IR-NOT:  riscv
// IR:      "llvm.return"
// IR-NOT:  riscv
// IR:      "sym_name" = "zero_int"
// IR-NOT:  riscv
// IR:      "llvm.mlir.zero"
// IR-NOT:  riscv
// IR:      "llvm.return"
// IR:      "sym_name" = "read"
// IR:      "riscv.la"

// CHECK: @by_region = internal global i32 7
// CHECK: @points_to = global ptr @by_region
// CHECK: @null_ptr = global ptr zeroinitializer
// CHECK: @zero_int = global i64 zeroinitializer
// CHECK: @function_ptr = global ptr @external_function
// CHECK: declare void @external_function()
// CHECK-LABEL: name: read
// CHECK:       PseudoLLA @zero_int
