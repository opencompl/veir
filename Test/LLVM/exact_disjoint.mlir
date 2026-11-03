// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i64)>, linkage = #llvm.linkage<external>, sym_name = "flags"}> ({
  ^bb0(%a: i64):
    %0 = "llvm.sdiv"(%a, %a) <{isExact}> : (i64, i64) -> i64
    %1 = "llvm.udiv"(%a, %a) <{isExact}> : (i64, i64) -> i64
    %2 = "llvm.lshr"(%a, %a) <{isExact}> : (i64, i64) -> i64
    %3 = "llvm.ashr"(%a, %a) <{isExact}> : (i64, i64) -> i64
    %4 = "llvm.or"(%a, %a) <{isDisjoint}> : (i64, i64) -> i64
    %5 = "llvm.sdiv"(%a, %a) : (i64, i64) -> i64
    %6 = "llvm.or"(%a, %a) : (i64, i64) -> i64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.sdiv"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) <{isExact}> : (i64, i64) -> i64
// CHECK: "llvm.udiv"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) <{isExact}> : (i64, i64) -> i64
// CHECK: "llvm.lshr"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) <{isExact}> : (i64, i64) -> i64
// CHECK: "llvm.ashr"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) <{isExact}> : (i64, i64) -> i64
// CHECK: "llvm.or"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) <{isDisjoint}> : (i64, i64) -> i64
// CHECK: "llvm.sdiv"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) : (i64, i64) -> i64
// CHECK: "llvm.or"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) : (i64, i64) -> i64
