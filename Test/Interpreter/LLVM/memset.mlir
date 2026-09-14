// RUN: veir-interpret %s | filecheck %s

// `memset` fills value bytes; a `memset` past the end of the object is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %byte = "llvm.mlir.constant"() <{value = 171 : i8}> : () -> i8
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.memset"(%a, %byte, %eight) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    %r = "llvm.load"(%a) : (!llvm.ptr) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xabababababababab#64]
