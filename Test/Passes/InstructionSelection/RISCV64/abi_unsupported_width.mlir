// RUN: veir-opt %s --print-op-generic -p=call-lowering-riscv64 | filecheck %s

// A function with any boundary type that is not passed in a single register is
// left entirely unlowered, rather than having only its other boundaries coerced.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "void_i17", function_type = !llvm.func<void (i17, i64)>}> ({
  ^bb0(%x: i17, %y: i64):
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<void (i17, i64)>, "sym_name" = "void_i17"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : i17, %{{.*}} : i64):
  // CHECK-NEXT: "llvm.return"() : () -> ()

  "llvm.func"() <{sym_name = "ret_i44", function_type = !llvm.func<i44 (i64)>}> ({
  ^bb0(%y: i64):
    %t = "llvm.trunc"(%y) : (i64) -> i44
    "llvm.return"(%t) : (i44) -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<i44 (i64)>, "sym_name" = "ret_i44"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : i64):
  // CHECK: "llvm.return"(%{{.*}}) : (i44) -> ()
}) : () -> ()
