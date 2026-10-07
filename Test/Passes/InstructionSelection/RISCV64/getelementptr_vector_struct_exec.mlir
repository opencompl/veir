// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p=isel-riscv64 > %t.partial
// RUN: filecheck %s --input-file=%t.partial
// RUN: veir-interpret %t.partial | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p=riscv > %t
// RUN: filecheck %s --input-file=%t
// RUN: veir-interpret %t | filecheck %s --check-prefix=EXEC

// Write at byte offsets determined by LLVM's RV64 layout, then read through
// struct GEPs. Shared layout errors in interpretation and lowering must not
// let this test pass. No vector-valued loads or stores are required.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    // Eight i1 elements occupy one byte, putting the next field at offset 1.
    %bits = "llvm.alloca"(%one) <{elem_type = !llvm.struct<(vector<8xi1>, i8)>}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 2 : i64}>
    // Five i24 elements occupy 15 bytes, rounded to a 16-byte allocation.
    %odd = "llvm.alloca"(%one) <{elem_type = !llvm.struct<(vector<5xi24>, i8)>}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 16 : i64, "size" = 32 : i64}>
    // A packed struct still uses the vector's four-byte allocation size.
    %packed = "llvm.alloca"(%one) <{elem_type = !llvm.struct<packed (i8, vector<17xi1>, i8)>}> : (i64) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 6 : i64}>

    %byte1 = "llvm.getelementptr"(%bits) <{elem_type = i8, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %byte16 = "llvm.getelementptr"(%odd) <{elem_type = i8, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    %byte5 = "llvm.getelementptr"(%packed) <{elem_type = i8, rawConstantIndices = array<i32: 5>}> : (!llvm.ptr) -> !llvm.ptr
    %seven = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %eleven = "llvm.mlir.constant"() <{value = 11 : i8}> : () -> i8
    %thirteen = "llvm.mlir.constant"() <{value = 13 : i8}> : () -> i8
    "llvm.store"(%seven, %byte1) : (i8, !llvm.ptr) -> ()
    "llvm.store"(%eleven, %byte16) : (i8, !llvm.ptr) -> ()
    "llvm.store"(%thirteen, %byte5) : (i8, !llvm.ptr) -> ()

    %field1 = "llvm.getelementptr"(%bits) <{elem_type = !llvm.struct<(vector<8xi1>, i8)>, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %field16 = "llvm.getelementptr"(%odd) <{elem_type = !llvm.struct<(vector<5xi24>, i8)>, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %field5 = "llvm.getelementptr"(%packed) <{elem_type = !llvm.struct<packed (i8, vector<17xi1>, i8)>, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %a = "llvm.load"(%field1) : (!llvm.ptr) -> i8
    // CHECK: "riscv.lb"{{.*}}<{"value" = 1 : i64}>
    %b = "llvm.load"(%field16) : (!llvm.ptr) -> i8
    // CHECK: "riscv.lb"{{.*}}<{"value" = 16 : i64}>
    %c = "llvm.load"(%field5) : (!llvm.ptr) -> i8
    // CHECK: "riscv.lb"{{.*}}<{"value" = 5 : i64}>
    %aw = "llvm.zext"(%a) : (i8) -> i64
    %bw = "llvm.zext"(%b) : (i8) -> i64
    %cw = "llvm.zext"(%c) : (i8) -> i64
    %ab = "llvm.add"(%aw, %bw) : (i64, i64) -> i64
    %result = "llvm.add"(%ab, %cw) : (i64, i64) -> i64
    "llvm.return"(%result) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x000000000000001f#64]
