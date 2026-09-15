// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Folding an address must use the index's value, including sign-extension
// from i8 and zero-extension from i1, rather than the raw attribute literal.
"builtin.module"() ({
  "func.func"() <{sym_name = "offset_constants", function_type = (!llvm.ptr, i8) -> i8}> ({
  ^bb0(%base: !llvm.ptr, %value: i8):
    // This index is -1: fold it into the store's offset.
    %negative = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i64
    %before = "llvm.getelementptr"(%base, %negative) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%value, %before) : (i8, !llvm.ptr) -> ()

    // This index is +1: fold it into the load's offset.
    %positive = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %after = "llvm.getelementptr"(%base, %positive) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %loaded = "llvm.load"(%after) : (!llvm.ptr) -> i8
    "func.return"(%loaded) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @offset_constants
// CHECK-SAME: (%[[BASE:.*]]: !llvm.ptr, %[[VALUE:.*]]: i8)
// CHECK-NEXT: %[[STORE_BASE:.*]] = "builtin.unrealized_conversion_cast"(%[[BASE]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT: %[[STORE_VALUE:.*]] = "builtin.unrealized_conversion_cast"(%[[VALUE]]) : (i8) -> !riscv.reg
// CHECK-NEXT: "riscv.sb"(%[[STORE_VALUE]], %[[STORE_BASE]]) <{"value" = -1 : i64}>
// CHECK-NEXT: %[[LOAD_BASE:.*]] = "builtin.unrealized_conversion_cast"(%[[BASE]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT: %[[LOAD:.*]] = "riscv.lb"(%[[LOAD_BASE]]) <{"value" = 1 : i64}>
// CHECK-NEXT: %[[RESULT:.*]] = "builtin.unrealized_conversion_cast"(%[[LOAD]]) : (!riscv.reg) -> i8
// CHECK-NEXT: "func.return"(%[[RESULT]]) : (i8) -> ()
