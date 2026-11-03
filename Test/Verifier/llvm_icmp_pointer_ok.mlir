// RUN: veir-opt %s | filecheck %s

// llvm.icmp compares pointers as well as integers.

"builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, !llvm.ptr) -> i1, sym_name = "main"}> ({
  ^bb0(%a: !llvm.ptr, %b: !llvm.ptr):
    %cmp = "llvm.icmp"(%a, %b) <{ predicate = 0 : i64 }> : (!llvm.ptr, !llvm.ptr) -> i1
    "func.return"(%cmp) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
