// RUN: veir-opt %s -p=arith-to-llvm | filecheck %s

// Sanity check for the 1:1 lowerings: ops map to their llvm counterpart with the
// same types (no casts) and flags preserved. The complicated expansions have
// their own dedicated tests.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "main"}> ({
    ^bb0(%0 : i32, %1 : i32):
      %a = "arith.subi"(%0, %1) <{overflowFlags = #arith.overflow<nsw, nuw>}> : (i32, i32) -> i32
      %b = "arith.ori"(%a, %1) <{disjoint}> : (i32, i32) -> i32
      "func.return"(%b) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      [[A:%.*]] = "llvm.sub"({{.*}}) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
// CHECK-NEXT: [[B:%.*]] = "llvm.or"([[A]], {{.*}}) <{disjoint}> : (i32, i32) -> i32
// CHECK-NOT: "arith.
