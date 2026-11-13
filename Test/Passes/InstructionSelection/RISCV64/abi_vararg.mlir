// RUN: veir-opt %s --print-op-generic -p=call-lowering-riscv64 | filecheck %s

// A variadic function is left entirely unlowered, even when its fixed
// arguments are all passed in registers: its variadic arguments are not modeled.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "vararg", function_type = !llvm.func<i64 (i64, ...)>}> ({
  ^bb0(%x: i64):
    "llvm.return"(%x) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<i64 (i64, ...)>, "sym_name" = "vararg"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : i64):
  // CHECK-NEXT: "llvm.return"(%{{.*}}) : (i64) -> ()
}) : () -> ()
