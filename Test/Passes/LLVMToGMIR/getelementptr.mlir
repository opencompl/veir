// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// Each index is sign-extended or truncated to `i64` and multiplied by its stride. It is
// added after the constant offset before it, and the remaining constant offset comes last.

"builtin.module"() ({
  // Wider indices are truncated to `i64`.
  "func.func"() <{function_type = (!llvm.ptr, i128) -> (), sym_name = "trunc"}> ({
  ^bb0(%p: !llvm.ptr, %j: i128):
    // CHECK-LABEL: func.func @trunc(
    // CHECK-SAME: %[[P:[^:]*]]: !llvm.ptr, %[[J:[^:]*]]: i128
    // CHECK-NEXT: %[[TJ:.*]] = "gmir.g_trunc"(%[[J]]) : (i128) -> i64
    // CHECK-NEXT: %[[GJ:.*]] = "gmir.g_ptr_add"(%[[P]], %[[TJ]])
    // CHECK-NEXT: "test.test"(%[[GJ]])
    %gj = "llvm.getelementptr"(%p, %j) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i128) -> !llvm.ptr
    "test.test"(%gj) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // The offset accumulated before an index is added before it:
  // {i8, [2 x i16]}: the array is at offset 2, so `p[1].1[i]` is `(p + 6 + 2) + i * 2`.
  "func.func"() <{function_type = (!llvm.ptr, i64) -> (), sym_name = "flush"}> ({
  ^bb0(%p: !llvm.ptr, %i: i64):
    // CHECK-LABEL: func.func @flush(
    // CHECK-SAME: %[[P:[^:]*]]: !llvm.ptr, %[[I:[^:]*]]: i64
    // CHECK-NEXT: %[[C:.*]] = "gmir.g_constant"() <{"value" = 8 : i64}> : () -> i64
    // CHECK-NEXT: %[[B:.*]] = "gmir.g_ptr_add"(%[[P]], %[[C]])
    // CHECK-NEXT: %[[S:.*]] = "gmir.g_constant"() <{"value" = 2 : i64}> : () -> i64
    // CHECK-NEXT: %[[M:.*]] = "gmir.g_mul"(%[[I]], %[[S]])
    // CHECK-NEXT: %[[G:.*]] = "gmir.g_ptr_add"(%[[B]], %[[M]])
    // CHECK-NEXT: "test.test"(%[[G]])
    %g = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.struct<(i8, !llvm.array<2 x i16>)>, rawConstantIndices = array<i32: 1, 1, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%g) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
