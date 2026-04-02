// RUN: veir-opt %s -p=dce| filecheck %s

"builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6():
        %1 = "llvm.constant"() <{"value" = 1 : i64}> : () -> i64
        %2 = "llvm.constant"() <{"value" = 2 : i64}> : () -> i64
        %3 = "llvm.constant"() <{"value" = 3 : i64}> : () -> i64
        %4 = "llvm.add"(%1, %2) : (i64, i64) -> i64
        "llvm.return"(%4) : (i64) -> ()
        // CHECK:      %{{.*}} = "llvm.constant"() <{"value" = 1 : i64}> : () -> i64
        // CHECK-NEXT: %{{.*}} = "llvm.constant"() <{"value" = 2 : i64}> : () -> i64
        // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
        // CHECK-NEXT: "llvm.return"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
