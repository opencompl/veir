// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr, i64)>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr, %i: i64):
    // The first index steps over whole structs, so it can be negative.
    %first = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<(i8, i64)>, rawConstantIndices = array<i32: -3, 1>}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: -3, 1>

    // An empty struct is valid when no field is selected.
    %empty = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<()>, rawConstantIndices = array<i32: -1>}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: -1>

    // Walk through a struct, an array, and a packed struct. Array indices may
    // be negative or dynamic, but the final struct index must be constant.
    %nested = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.struct<(i8, array<2 x struct<packed (i32, i64)>>)>, rawConstantIndices = array<i32: -2147483648, 1, -3, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: -2147483648, 1, -3, 1>
    %dynamic = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.struct<(i8, array<2 x struct<packed (i32, i64)>>)>, rawConstantIndices = array<i32: 0, 1, -2147483648, 0>}> : (!llvm.ptr, i64) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: 0, 1, -2147483648, 0>

    // Array and vector indices may also exceed the element count.
    %array = "llvm.getelementptr"(%p) <{elem_type = !llvm.array<2 x struct<(i8, i64)>>, rawConstantIndices = array<i32: 0, 100, 0>}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: 0, 100, 0>
    %vector = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<(vector<4xi32>, i8)>, rawConstantIndices = array<i32: 0, 0, 100>}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: 0, 0, 100>

    // Named structs with a body are checked too.
    %named = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<"named", (i8, i64)>, rawConstantIndices = array<i32: 0, 0>}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: 0, 0>
    // VeIR keeps structs with unsupported field types opaque, so stop the
    // type walk instead of rejecting a valid field selection.
    %opaque = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<(ptr<1>, i64)>, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: 0, 1>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
