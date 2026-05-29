// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"() ({
^bb0(%ptr : !llvm.ptr):
    %load0 = "llvm.load"(%ptr) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
    %load1 = "llvm.load"(%ptr) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
    "test.test"(%load0, %load1) : (i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : !llvm.ptr):
    // CHECK-NEXT: %[[LOAD0:.*]] = "llvm.load"(%{{.*}}) <{{.*}}> : (!llvm.ptr) -> i32
    // CHECK-NEXT: %[[LOAD1:.*]] = "llvm.load"(%{{.*}}) <{{.*}}> : (!llvm.ptr) -> i32
    // CHECK-NEXT: "test.test"(%[[LOAD0]], %[[LOAD1]]) : (i32, i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
