// RUN: veir-opt %s | filecheck %s
//
// Tests for llvm.getelementptr with 1, 2, 3, and 4 dynamic indices.
// The operand count must equal 1 (base pointer) + number of kDynamic
// (-2147483648) entries in rawConstantIndices.

"builtin.module"() ({
  "llvm.func"() ({
    ^bb0(%ptr: !llvm.ptr, %i: i64, %j: i64, %k: i64, %l: i64):

      // 1 dynamic index: ptr[i]
      %g1 = "llvm.getelementptr"(%ptr, %i) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr

      // 2 dynamic indices: ptr[i][j]
      %g2 = "llvm.getelementptr"(%ptr, %i, %j) <{elem_type = !llvm.array<10 x i8>, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr

      // 3 dynamic indices: ptr[i][j][k]
      %g3 = "llvm.getelementptr"(%ptr, %i, %j, %k) <{elem_type = !llvm.array<10 x array<10 x i8>>, rawConstantIndices = array<i32: -2147483648, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64, i64) -> !llvm.ptr

      // 4 dynamic indices: ptr[i][j][k][l]
      %g4 = "llvm.getelementptr"(%ptr, %i, %j, %k, %l) <{elem_type = !llvm.array<10 x array<10 x array<10 x i8>>>, rawConstantIndices = array<i32: -2147483648, -2147483648, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64, i64, i64) -> !llvm.ptr

      // 2 dynamic indices with an interleaved constant index: ptr[i][0][j]
      %g5 = "llvm.getelementptr"(%ptr, %i, %j) <{elem_type = !llvm.array<10 x i8>, rawConstantIndices = array<i32: -2147483648, 0, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr

      "llvm.return"(%g1, %g2, %g3, %g4, %g5) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
// CHECK-NEXT:      "llvm.func"() ({
// CHECK-NEXT:        ^{{.*}}(%{{.*}} : !llvm.ptr, %{{.*}} : i64, %{{.*}} : i64, %{{.*}} : i64, %{{.*}} : i64):
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = i8, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x i8>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x array<10 x i8>>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64, i64) -> !llvm.ptr
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x array<10 x array<10 x i8>>>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64, i64, i64) -> !llvm.ptr
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x i8>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, 0, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:          "llvm.return"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
// CHECK-NEXT:      }) : () -> ()
// CHECK-NEXT: }) : () -> ()
