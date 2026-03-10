// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %seven = "llvm.constant"() <{ "value" = 7 : i8 }> : () -> i8
  %nine = "llvm.constant"() <{ "value" = 9 : i8 }> : () -> i8
  %x = "llvm.icmp"(%seven, %nine) <{ "predicate" = "abc" }> : (i8, i8) -> i1
  "func.return"(%x) : (i1) -> ()
}) : () -> ()

// CHECK: Error while interpreting module
