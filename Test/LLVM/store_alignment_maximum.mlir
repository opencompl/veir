// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// The largest alignment LLVM supports, 2^32, is accepted.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %v = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.store"(%v, %p) <{alignment = 4294967296 : i64}> : (i32, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.store"({{.*}}) <{"alignment" = 4294967296 : i64}>
