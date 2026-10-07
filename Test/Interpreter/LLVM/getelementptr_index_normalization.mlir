// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC

// GEP's raw indices are signed i32 values even when written as unsigned
// literals. This applies both to constant indices and the dynamic sentinel.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %p = "llvm.alloca"(%four) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %expected = "llvm.getelementptr"(%p) <{elem_type = i8, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %value = "llvm.mlir.constant"() <{value = 42 : i8}> : () -> i8
    "llvm.store"(%value, %expected) : (i8, !llvm.ptr) -> ()
    %base = "llvm.getelementptr"(%p) <{elem_type = i8, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr

    // Both addresses must point back to p[1]. The second GEP exercises
    // the unsigned spelling of the dynamic-index sentinel.
    %constant = "llvm.getelementptr"(%base) <{elem_type = i8, rawConstantIndices = array<i32: 4294967295>}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: -1>
    %zeroIndex = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %dynamic = "llvm.getelementptr"(%constant, %zeroIndex) <{elem_type = i8, rawConstantIndices = array<i32: 2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    // CHECK: "llvm.getelementptr"{{.*}}"rawConstantIndices" = array<i32: -2147483648>
    %a = "llvm.load"(%constant) : (!llvm.ptr) -> i8
    %b = "llvm.load"(%dynamic) : (!llvm.ptr) -> i8
    %aw = "llvm.zext"(%a) : (i8) -> i64
    %bw = "llvm.zext"(%b) : (i8) -> i64
    %sum = "llvm.add"(%aw, %bw) : (i64, i64) -> i64
    "llvm.return"(%sum) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x0000000000000054#64]
