// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() ({
    ^bb0(%a: i32, %b: i32):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
        // CHECK:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
        
    ^bb1(%a: i32, %b: i32):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        // CHECK:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        
    ^bb2(%a: i64, %b: i32):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 6 : i64}> : (i64, i32) -> i1
        // CHECK:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 6 : i64}> : (i64, i32) -> i1
    
    ^bb3(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 11 : i64}> : (i64, i64) -> i1
        // CHECK:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 11 : i64}> : (i64, i64) -> i1
  }) : () -> ()
}) : () -> ()

