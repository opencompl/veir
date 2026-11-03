// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%i: i32):
    %a = "llvm.zext"(%i) <{nonNeg}> : (i32) -> i64
    %b = "llvm.zext"(%i) : (i32) -> i64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.zext"(%{{[a-z0-9_]+}}) <{nonNeg}> : (i32) -> i64
// CHECK: "llvm.zext"(%{{[a-z0-9_]+}}) : (i32) -> i64
