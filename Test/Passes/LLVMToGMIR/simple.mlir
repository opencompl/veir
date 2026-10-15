// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    ^bb0():
      %a = "llvm.mlir.constant"() <{value = 100 : i16}> : () -> i16
      %b = "llvm.mlir.constant"() <{value = 42 : i16}> : () -> i16
      %add = "llvm.add"(%a, %b) <{overflowFlags = 3 : i32}> : (i16, i16) -> i16
      %sub = "llvm.sub"(%a, %b) : (i16, i16) -> i16
      %cmp = "llvm.icmp"(%a, %b) <{predicate = 4 : i64}> : (i16, i16) -> i1
      %sext = "llvm.sext"(%a) : (i16) -> i32
      %zext = "llvm.zext"(%a) <{nonNeg}> : (i16) -> i32
      %trunc = "llvm.trunc"(%a) <{overflowFlags = 1 : i32}> : (i16) -> i8
      %and = "llvm.and"(%a, %b) : (i16, i16) -> i16
      %or = "llvm.or"(%a, %b) <{isDisjoint}> : (i16, i16) -> i16
      %xor = "llvm.xor"(%a, %b) : (i16, i16) -> i16
      "test.test"(%add, %sub, %cmp, %sext, %zext, %trunc, %and, %or, %xor) : (i16, i16, i1, i32, i32, i8, i16, i16, i16) -> ()
      "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "builtin.module"
// CHECK: "gmir.g_add"
// CHECK-SAME: "overflowFlags" = 3 : i32
// CHECK: "gmir.g_sub"
// CHECK: "gmir.g_icmp"
// CHECK-SAME: "predicate" = 4 : i64
// CHECK: "gmir.g_sext"(%{{.*}}) : (i16) -> i32
// CHECK: "gmir.g_zext"(%{{.*}}) <{nonNeg}> : (i16) -> i32
// CHECK: "gmir.g_trunc"(%{{.*}}) <{"overflowFlags" = 1 : i32}> : (i16) -> i8
// CHECK: "gmir.g_and"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
// CHECK: "gmir.g_or"(%{{.*}}, %{{.*}}) <{isDisjoint}> : (i16, i16) -> i16
// CHECK: "gmir.g_xor"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
