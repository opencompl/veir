// RUN: VEIR_UNREGISTERED_ROUNDTRIP
//
// Tests for llvm.getelementptr with 1, 2, 3, and 4 dynamic indices.
// The operand count must equal 1 (base pointer) + number of kDynamic
// (-2147483648) entries in rawConstantIndices.

"builtin.module"() ({
  "llvm.func"()  <{function_type = !llvm.func<void (!llvm.ptr, i64, i64, i64, i64)>}> ({
    ^bb0(%ptr: !llvm.ptr, %i: i64, %j: i64, %k: i64, %l: i64):

      // 1 dynamic index: ptr[i]
      %g1 = "llvm.getelementptr"(%ptr, %i) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr

      // 2 dynamic indices: ptr[i][j]
      %g2 = "llvm.getelementptr"(%ptr, %i, %j) <{elem_type = !llvm.array<10 x i8>, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr

      // 3 dynamic indices: ptr[i][j][k]
      %g3 = "llvm.getelementptr"(%ptr, %i, %j, %k) <{elem_type = !llvm.array<10 x array<10 x i8>>, rawConstantIndices = array<i32: -2147483648, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64, i64) -> !llvm.ptr

      // 4 dynamic indices: ptr[i][j][k][l]
      %g4 = "llvm.getelementptr"(%ptr, %i, %j, %k, %l) <{elem_type = !llvm.array<10 x !llvm.array<10 x !llvm.array<10 x i8>>>, rawConstantIndices = array<i32: -2147483648, -2147483648, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64, i64, i64) -> !llvm.ptr

      // 2 dynamic indices with an interleaved constant index: ptr[i][0][j]
      %g5 = "llvm.getelementptr"(%ptr, %i, %j) <{elem_type = !llvm.array<10 x i8>, rawConstantIndices = array<i32: -2147483648, 0, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr

      "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "gep_no_wrap_flags", visibility_ = 0 : i64}> ({
  ^bb15(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    // getelementptr inbounds float, ptr %ptr, i32 7
    %1 = "llvm.getelementptr"(%arg0, %0) <{elem_type = f32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    // getelementptr nusw float, ptr %ptr, i32 7
    %2 = "llvm.getelementptr"(%arg0, %0) <{elem_type = f32, noWrapFlags = 2 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    // getelementptr nuw float, ptr %ptr, i32 7
    %3 = "llvm.getelementptr"(%arg0, %0) <{elem_type = f32, noWrapFlags = 4 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    // getelementptr nusw nuw float, ptr %ptr, i32 7
    %4 = "llvm.getelementptr"(%arg0, %0) <{elem_type = f32, noWrapFlags = 6 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
// CHECK-NEXT:      "llvm.func"() <{"function_type" = !llvm.func<void (!llvm.ptr, i64, i64, i64, i64)>}> ({
// CHECK-NEXT:        ^{{.*}}(%{{.*}} : !llvm.ptr, %{{.*}} : i64, %{{.*}} : i64, %{{.*}} : i64, %{{.*}} : i64):
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = i8, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x i8>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x !llvm.array<10 x i8>>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64, i64) -> !llvm.ptr
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x !llvm.array<10 x !llvm.array<10 x i8>>>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64, i64, i64) -> !llvm.ptr
// CHECK-NEXT:          %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x i8>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, 0, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:          "llvm.return"() : () -> ()
// CHECK-NEXT:      }) : () -> ()

// CHECK-NEXT:  "llvm.func"()
// CHECK-NEXT:  ^15(%{{.*}}: !llvm.ptr):
// CHECK-NEXT:    %{{.*}} = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:    %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = f32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
// CHECK-NEXT:    %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = f32, "noWrapFlags" = 2 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
// CHECK-NEXT:    %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = f32, "noWrapFlags" = 4 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
// CHECK-NEXT:    %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = f32, "noWrapFlags" = 6 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
// CHECK-NEXT:    "llvm.return"() : () -> ()
// CHECK-NEXT:  }) : () -> ()
// CHECK-NEXT: }) : () -> ()
