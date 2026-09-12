// RUN: veir-interpret %s | filecheck %s

// `ptrtoint` yields the physical address and `inttoptr` finds the object
// at an address again, including at an offset into it.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i32)}> ({
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 19 : i32}> : () -> i32
    %a = "llvm.alloca"(%two) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %a1 = "llvm.getelementptr"(%a, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %a1) : (i32, !llvm.ptr) -> ()
    %addr = "llvm.ptrtoint"(%a) : (!llvm.ptr) -> i64
    %addr1 = "llvm.add"(%addr, %four) : (i64, i64) -> i64
    %p = "llvm.inttoptr"(%addr1) : (i64) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i32
    "func.return"(%addr, %r) : (i64, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000010#64, 0x00000013#32]
