// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %a = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
      %b = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
      %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
      %c2 = "llvm.icmp"(%a, %b) <{predicate = 2 : i64}> : (i64, i64) -> i1
      %t2 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
      %z2 = "llvm.select"(%c2, %t2, %zero) : (i1, i64, i64) -> i64
      %acc0 = "llvm.or"(%zero, %z2) : (i64, i64) -> i64
      %c3 = "llvm.icmp"(%a, %b) <{predicate = 3 : i64}> : (i64, i64) -> i1
      %t3 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
      %z3 = "llvm.select"(%c3, %t3, %zero) : (i1, i64, i64) -> i64
      %acc1 = "llvm.or"(%acc0, %z3) : (i64, i64) -> i64
      %c4 = "llvm.icmp"(%a, %b) <{predicate = 4 : i64}> : (i64, i64) -> i1
      %t4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
      %z4 = "llvm.select"(%c4, %t4, %zero) : (i1, i64, i64) -> i64
      %acc2 = "llvm.or"(%acc1, %z4) : (i64, i64) -> i64
      %c5 = "llvm.icmp"(%a, %b) <{predicate = 5 : i64}> : (i64, i64) -> i1
      %t5 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
      %z5 = "llvm.select"(%c5, %t5, %zero) : (i1, i64, i64) -> i64
      %acc3 = "llvm.or"(%acc2, %z5) : (i64, i64) -> i64
      %c6 = "llvm.icmp"(%a, %b) <{predicate = 6 : i64}> : (i64, i64) -> i1
      %t6 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
      %z6 = "llvm.select"(%c6, %t6, %zero) : (i1, i64, i64) -> i64
      %acc4 = "llvm.or"(%acc3, %z6) : (i64, i64) -> i64
      %c7 = "llvm.icmp"(%a, %b) <{predicate = 7 : i64}> : (i64, i64) -> i1
      %t7 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
      %z7 = "llvm.select"(%c7, %t7, %zero) : (i1, i64, i64) -> i64
      %acc5 = "llvm.or"(%acc4, %z7) : (i64, i64) -> i64
      %c8 = "llvm.icmp"(%a, %b) <{predicate = 8 : i64}> : (i64, i64) -> i1
      %t8 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
      %z8 = "llvm.select"(%c8, %t8, %zero) : (i1, i64, i64) -> i64
      %acc6 = "llvm.or"(%acc5, %z8) : (i64, i64) -> i64
      %c9 = "llvm.icmp"(%a, %b) <{predicate = 9 : i64}> : (i64, i64) -> i1
      %t9 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
      %z9 = "llvm.select"(%c9, %t9, %zero) : (i1, i64, i64) -> i64
      %acc7 = "llvm.or"(%acc6, %z9) : (i64, i64) -> i64
      "llvm.return"(%acc7) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000000000000cc#64]
// CHECK: Program output: #[0x00000000000000cc#64]
