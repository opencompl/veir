// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<ptr (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "align_down"}> ({
  ^bb0(%p: !llvm.ptr):
    %addr = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    %mask = "llvm.mlir.constant"() <{value = -8 : i64}> : () -> i64
    %down = "llvm.and"(%addr, %mask) : (i64, i64) -> i64
    %q = "llvm.inttoptr"(%down) : (i64) -> !llvm.ptr
    "llvm.return"(%q) : (!llvm.ptr) -> ()
  }) : () -> ()
  // A narrower integer side than the pointer width.
  "llvm.func"() <{function_type = !llvm.func<i32 (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "low_bits"}> ({
  ^bb0(%p: !llvm.ptr):
    %addr = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i32
    "llvm.return"(%addr) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.ptrtoint"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> i64
// CHECK: "llvm.inttoptr"(%{{[a-z0-9_]+}}) : (i64) -> !llvm.ptr
// CHECK: "llvm.ptrtoint"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> i32
