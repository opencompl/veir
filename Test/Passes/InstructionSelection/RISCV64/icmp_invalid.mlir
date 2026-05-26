// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() ({
    ^bb0(%a: i32, %b: i32, %c: i64):
        %r_0 = "llvm.icmp"(%a, %b) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
        // CHECK:           "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
        %r_2 = "llvm.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        // CHECK-NEXT:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        %r_6 = "llvm.icmp"(%c, %b) <{"predicate" = 6 : i64}> : (i64, i32) -> i1
        // CHECK-NEXT:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 6 : i64}> : (i64, i32) -> i1
  }) : () -> ()
}) : () -> ()
