// RUN: veir-interpret %s | filecheck %s --check-prefix=RESULT
// RUN: veir-opt %s --print-op-generic -p=isel-riscv64 > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=RESULT
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// Folding an address must use the index's value, including sign-extension
// from i8 and zero-extension from i1, rather than the raw attribute literal.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8)}> ({
    %size = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %mem = "llvm.alloca"(%size) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %five = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %base = "llvm.getelementptr"(%mem, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr

    // This index is -1: store at mem + 3, then read through a separate address.
    %negative = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i64
    %before = "llvm.getelementptr"(%base, %negative) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %v42 = "llvm.mlir.constant"() <{value = 42 : i8}> : () -> i8
    "llvm.store"(%v42, %before) : (i8, !llvm.ptr) -> ()
    %at3 = "llvm.getelementptr"(%mem, %three) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %stored = "llvm.load"(%at3) : (!llvm.ptr) -> i8

    // This index is +1: load the value stored separately at mem + 5.
    %positive = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %at5 = "llvm.getelementptr"(%mem, %five) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %v43 = "llvm.mlir.constant"() <{value = 43 : i8}> : () -> i8
    "llvm.store"(%v43, %at5) : (i8, !llvm.ptr) -> ()
    %after = "llvm.getelementptr"(%base, %positive) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %loaded = "llvm.load"(%after) : (!llvm.ptr) -> i8
    "func.return"(%stored, %loaded) : (i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// RESULT: Program output: #[0x2a#8, 0x2b#8]
// ISEL: "riscv.sb"({{.*}}) <{"value" = -1 : i64}>
// ISEL: "riscv.lb"({{.*}}) <{"value" = 1 : i64}>
