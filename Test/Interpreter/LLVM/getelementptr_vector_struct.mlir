// RUN: veir-interpret %s | filecheck %s

// A packed struct still uses the vector's four-byte allocation size, placing
// the final i8 at offset 5. Write at that byte offset, then read through a
// struct GEP to check the layout without vector-valued loads or stores.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %packed = "llvm.alloca"(%one) <{elem_type = !llvm.struct<packed (i8, vector<17xi1>, i8)>}> : (i64) -> !llvm.ptr

    %byte5 = "llvm.getelementptr"(%packed) <{elem_type = i8, rawConstantIndices = array<i32: 5>}> : (!llvm.ptr) -> !llvm.ptr
    %thirteen = "llvm.mlir.constant"() <{value = 13 : i8}> : () -> i8
    "llvm.store"(%thirteen, %byte5) : (i8, !llvm.ptr) -> ()

    %field5 = "llvm.getelementptr"(%packed) <{elem_type = !llvm.struct<packed (i8, vector<17xi1>, i8)>, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %value = "llvm.load"(%field5) : (!llvm.ptr) -> i8
    %result = "llvm.zext"(%value) : (i8) -> i64
    "llvm.return"(%result) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000d#64]
