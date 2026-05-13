// RUN: veir-interpret %s | filecheck %s

// `sdiv poison, -1` (width > 1) is immediate UB: the poison dividend could
// refine to intMin, in which case the overflow case applies.
"builtin.module"() ({
  %neg1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %one  = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
  %poison = "llvm.add"(%neg1, %one) <{nuw}> : (i32, i32) -> i32
  %y = "llvm.sdiv"(%poison, %neg1) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
