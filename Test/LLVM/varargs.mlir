// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32, ...)>, linkage = #llvm.linkage<external>, sym_name = "sum"}> ({
  ^bb0(%n: i32):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %list = "llvm.alloca"(%one) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.intr.vastart"(%list) : (!llvm.ptr) -> ()
    %i = "llvm.va_arg"(%list) : (!llvm.ptr) -> i32
    %f = "llvm.va_arg"(%list) : (!llvm.ptr) -> f64
    %p = "llvm.va_arg"(%list) : (!llvm.ptr) -> !llvm.ptr
    "llvm.intr.vaend"(%list) : (!llvm.ptr) -> ()
    "llvm.return"(%i) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.vastart"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> ()
// CHECK: "llvm.va_arg"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> i32
// CHECK: "llvm.va_arg"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> f64
// CHECK: "llvm.va_arg"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> !llvm.ptr
// CHECK: "llvm.intr.vaend"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> ()
