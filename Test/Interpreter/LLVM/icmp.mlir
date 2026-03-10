// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %seven = "llvm.constant"() <{ "value" = 7 : i8 }> : () -> i8
  %nine = "llvm.constant"() <{ "value" = 9 : i8 }> : () -> i8
  %x = "llvm.icmp"(%seven, %nine) <{ "predicate" = "eq" }> : (i8, i8) -> i1
  %y = "llvm.icmp"(%seven, %nine) <{ "predicate" = "ne" }> : (i8, i8) -> i1
  %z = "llvm.icmp"(%seven, %nine) <{ "predicate" = "ugt" }> : (i8, i8) -> i1
  %w = "llvm.icmp"(%seven, %nine) <{ "predicate" = "slt" }> : (i8, i8) -> i1
  %v = "llvm.icmp"(%seven, %nine) <{ "predicate" = "ule" }> : (i8, i8) -> i1
  %u = "llvm.icmp"(%seven, %nine) <{ "predicate" = "sle" }> : (i8, i8) -> i1
  %s = "llvm.icmp"(%seven, %nine) <{ "predicate" = "sgt" }> : (i8, i8) -> i1
  %p = "llvm.icmp"(%seven, %nine) <{ "predicate" = "uge" }> : (i8, i8) -> i1
  %q = "llvm.icmp"(%seven, %nine) <{ "predicate" = "sge" }> : (i8, i8) -> i1
  "func.return"(%x, %y, %z, %w, %v, %u, %s, %p, %q) : (i1, i1, i1, i1, i1, i1, i1, i1, i1) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0#1, 0x1#1, 0x0#1, 0x1#1, 0x1#1, 0x1#1, 0x0#1, 0x0#1, 0x0#1]
