// RUN: veir-interpret %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %0 = "arith.constant"() <{ "value" = 14 : i32 }> : () -> i32
    "func.return"(%0) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i16 ()>, linkage = #llvm.linkage<external>, sym_name = "main", unnamed_addr = 0 : i64, visibility_ = 0 : i64}> ({
    %1 = "llvm.mlir.constant"() <{value = 13 : i16}> : () -> i16
    "llvm.return"(%1) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error: Multiple entry points: define exactly one zero-argument function named 'main' or use only top-level executable ops
