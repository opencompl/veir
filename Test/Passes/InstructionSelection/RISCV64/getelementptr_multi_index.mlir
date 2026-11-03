// RUN: veir-opt %s -p=riscv | filecheck %s

// {i8, [3 x [5 x i64]], i64}: array at offset 8, final field at 128.
"builtin.module"() ({
  "func.func"() <{sym_name = "mixed_indices", function_type = (!llvm.ptr, i64, i32) -> ()}> ({
  ^bb0(%p: !llvm.ptr, %i: i64, %j: i32):
    // Address = p + i * 40 + sext(j) * 8 + 8.
    // The second dynamic index uses the unsigned spelling of the sentinel.
    %indexed = "llvm.getelementptr"(%p, %i, %j) <{elem_type = !llvm.struct<(i8, !llvm.array<3 x !llvm.array<5 x i64>>, i64)>, rawConstantIndices = array<i32: 0, 1, -2147483648, 2147483648>}> : (!llvm.ptr, i64, i32) -> !llvm.ptr
    // CHECK-LABEL: func.func @mixed_indices(
    // CHECK-SAME: %[[P:.*]]: !llvm.ptr, %[[I:.*]]: i64, %[[J:.*]]: i32)
    // CHECK-NEXT: %[[JR:.*]] = "builtin.unrealized_conversion_cast"(%[[J]]) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[SIGNED:.*]] = "riscv.sextw"(%[[JR]])
    // CHECK-NEXT: %[[BASE:.*]] = "builtin.unrealized_conversion_cast"(%[[P]]) : (!llvm.ptr) -> !riscv.reg
    // CHECK-NEXT: %[[IR:.*]] = "builtin.unrealized_conversion_cast"(%[[I]]) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[STRIDE:.*]] = "riscv.li"() <{"value" = 40 : i64}>
    // CHECK-NEXT: %[[SCALED:.*]] = "riscv.mul"(%[[IR]], %[[STRIDE]])
    // CHECK-NEXT: %[[ROW:.*]] = "riscv.add"(%[[BASE]], %[[SCALED]])
    // CHECK-NEXT: %[[ELEMENT:.*]] = "riscv.sh3add"(%[[SIGNED]], %[[ROW]])
    // CHECK-NEXT: %[[ADDR:.*]] = "riscv.addi"(%[[ELEMENT]]) <{"value" = 8 : i64}>
    // CHECK-NEXT: %[[RESULT:.*]] = "builtin.unrealized_conversion_cast"(%[[ADDR]]) : (!riscv.reg) -> !llvm.ptr
    // CHECK-NEXT: "test.test"(%[[RESULT]])
    "test.test"(%indexed) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "constant_field", function_type = (!llvm.ptr, i64) -> ()}> ({
  ^bb0(%p: !llvm.ptr, %value: i64):
    // Field 2's byte offset folds into both the store and the load.
    %field = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<(i8, !llvm.array<3 x !llvm.array<5 x i64>>, i64)>, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%value, %field) : (i64, !llvm.ptr) -> ()
    %loaded = "llvm.load"(%field) : (!llvm.ptr) -> i64
    // CHECK-LABEL: func.func @constant_field(
    // CHECK-SAME: %[[CP:.*]]: !llvm.ptr, %[[V:.*]]: i64)
    // CHECK-NEXT: %[[STORE_BASE:.*]] = "builtin.unrealized_conversion_cast"(%[[CP]]) : (!llvm.ptr) -> !riscv.reg
    // CHECK-NEXT: %[[VR:.*]] = "builtin.unrealized_conversion_cast"(%[[V]]) : (i64) -> !riscv.reg
    // CHECK-NEXT: "riscv.sd"(%[[VR]], %[[STORE_BASE]]) <{"value" = 128 : i64}>
    // CHECK-NEXT: %[[LOAD_BASE:.*]] = "builtin.unrealized_conversion_cast"(%[[CP]]) : (!llvm.ptr) -> !riscv.reg
    // CHECK-NEXT: %[[LOADED:.*]] = "riscv.ld"(%[[LOAD_BASE]]) <{"value" = 128 : i64}>
    // CHECK-NEXT: %[[VALUE:.*]] = "builtin.unrealized_conversion_cast"(%[[LOADED]]) : (!riscv.reg) -> i64
    // CHECK-NEXT: "test.test"(%[[VALUE]])
    "test.test"(%loaded) : (i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
