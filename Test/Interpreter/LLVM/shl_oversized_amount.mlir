// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %c = "llvm.mlir.constant"() <{ "value" = 18446744073709551616 : i66 }> : () -> i66
  %none = "llvm.shl"(%c, %c) : (i66, i66) -> i66
  %nsw = "llvm.shl"(%c, %c) <{nsw}> : (i66, i66) -> i66
  %nuw = "llvm.shl"(%c, %c) <{nuw}> : (i66, i66) -> i66
  %nsw_nuw = "llvm.shl"(%c, %c) <{nsw, nuw}> : (i66, i66) -> i66
  "func.return"(%none, %nsw, %nuw, %nsw_nuw) : (i66, i66, i66, i66) -> ()
}) : () -> ()

// CHECK: Program output: #[poison, poison, poison, poison]
