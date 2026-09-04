// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"()  <{function_type = !llvm.func<void (!llvm.ptr)>, sym_name = "foo"}> ({
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

  // Identical io operations are side-effecting, so none of them is merged.
  "func.func"() <{function_type = (!io.address, !llvm.ptr, i64) -> (), sym_name = "io"}> ({
  ^bb0(%peer : !io.address, %buf : !llvm.ptr, %len : i64):
    %rand0 = "io.rand"(%buf, %len) : (!llvm.ptr, i64) -> i64
    %rand1 = "io.rand"(%buf, %len) : (!llvm.ptr, i64) -> i64
    %recv0 = "io.recv"(%peer, %buf, %len) : (!io.address, !llvm.ptr, i64) -> i64
    %recv1 = "io.recv"(%peer, %buf, %len) : (!io.address, !llvm.ptr, i64) -> i64
    %send0 = "io.send"(%peer, %buf, %len) : (!io.address, !llvm.ptr, i64) -> i64
    %send1 = "io.send"(%peer, %buf, %len) : (!io.address, !llvm.ptr, i64) -> i64
    "test.test"(%rand0, %rand1, %recv0, %recv1, %send0, %send1) : (i64, i64, i64, i64, i64, i64) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : !io.address, %{{.*}} : !llvm.ptr, %{{.*}} : i64):
    // CHECK-NEXT: %[[RAND0:.*]] = "io.rand"(%{{.*}}, %{{.*}}) : (!llvm.ptr, i64) -> i64
    // CHECK-NEXT: %[[RAND1:.*]] = "io.rand"(%{{.*}}, %{{.*}}) : (!llvm.ptr, i64) -> i64
    // CHECK-NEXT: %[[RECV0:.*]] = "io.recv"(%{{.*}}, %{{.*}}, %{{.*}}) : (!io.address, !llvm.ptr, i64) -> i64
    // CHECK-NEXT: %[[RECV1:.*]] = "io.recv"(%{{.*}}, %{{.*}}, %{{.*}}) : (!io.address, !llvm.ptr, i64) -> i64
    // CHECK-NEXT: %[[SEND0:.*]] = "io.send"(%{{.*}}, %{{.*}}, %{{.*}}) : (!io.address, !llvm.ptr, i64) -> i64
    // CHECK-NEXT: %[[SEND1:.*]] = "io.send"(%{{.*}}, %{{.*}}, %{{.*}}) : (!io.address, !llvm.ptr, i64) -> i64
    // CHECK-NEXT: "test.test"(%[[RAND0]], %[[RAND1]], %[[RECV0]], %[[RECV1]], %[[SEND0]], %[[SEND1]]) : (i64, i64, i64, i64, i64, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
