// RUN: veir-opt %s -p=arith-to-llvm | filecheck %s

// arith.addui_extended has two results: the sum and an i1 unsigned-overflow flag.
// LLVM's uadd.with.overflow intrinsic is not in Veir's llvm dialect, so the carry
// is computed directly as `icmp ult sum, a` (predicate 6 = ult), matching the
// addui_extended interpreter case. Both results are replaced independently.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i1, sym_name = "main"}> ({
    ^bb0(%0 : i32, %1 : i32):
      %s:2 = "arith.addui_extended"(%0, %1) : (i32, i32) -> (i32, i1)
      "func.return"(%s#1) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[A:%.*]] : i32, [[B:%.*]] : i32):
// CHECK-NEXT:   [[SUM:%.*]] = "llvm.add"([[A]], [[B]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[CARRY:%.*]] = "llvm.icmp"([[SUM]], [[A]]) <{"predicate" = 6 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:   "func.return"([[CARRY]]) : (i1) -> ()
// CHECK-NOT: "arith.
