// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `llvm.intr.lifetime.start` and `llvm.intr.lifetime.end` bracket the live
// range of a stack object. Each takes the pointer and nothing else: LLVM 22
// dropped the size argument these intrinsics used to carry.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, linkage = #llvm.linkage<external>, sym_name = "scoped"}> ({
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%n) <{alignment = 4 : i64, elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%p) : (!llvm.ptr) -> ()
    %v = "llvm.load"(%p) <{alignment = 4 : i64}> : (!llvm.ptr) -> i32
    "llvm.intr.lifetime.end"(%p) : (!llvm.ptr) -> ()
    "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.lifetime.start"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> ()
// CHECK: "llvm.intr.lifetime.end"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> ()
