// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// Nonstandard calling conventions must survive on functions and calls.
// An explicit ccc, an omitted CConv, and fastcc all use the standard convention
// and remain eligible for lowering.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "fast", function_type = !llvm.func<i64 (i64)>, CConv = #llvm.cconv<fastcc>}> ({
  ^bb0(%a: i64):
    "llvm.return"(%a) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "CConv" = #llvm.cconv<fastcc>, "function_type" = !llvm.func<!riscv.reg (!riscv.reg)>, "sym_name" = "fast"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : !riscv.reg):
  // CHECK: "riscv_cf.return"(%{{.*}}) : (!riscv.reg) -> ()

  // A void return must remain unlowered even though it has no nonregister operands.
  "llvm.func"() <{sym_name = "ghc", function_type = !llvm.func<void (i64)>, CConv = #llvm.cconv<cc_10>}> ({
  ^bb0(%a: i64):
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "CConv" = #llvm.cconv<cc_10>, "function_type" = !llvm.func<void (i64)>, "sym_name" = "ghc"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : i64):
  // CHECK-NEXT: "llvm.return"() : () -> ()

  "llvm.func"() <{sym_name = "discardable", function_type = !llvm.func<i64 (i64)>}> ({
  ^bb0(%a: i64):
    "llvm.return"(%a) : (i64) -> ()
  }) {CConv = #llvm.cconv<fastcc>} : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<!riscv.reg (!riscv.reg)>, "sym_name" = "discardable"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : !riscv.reg):
  // CHECK: "riscv_cf.return"(%{{.*}}) : (!riscv.reg) -> ()
  // CHECK-NEXT: }) {"CConv" = #llvm.cconv<fastcc>}

  "llvm.func"() <{sym_name = "explicit", function_type = !llvm.func<i64 (i64)>, CConv = #llvm.cconv<ccc>}> ({
  ^bb0(%a: i64):
    "llvm.return"(%a) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "CConv" = #llvm.cconv<ccc>, "function_type" = !llvm.func<!riscv.reg (!riscv.reg)>, "sym_name" = "explicit"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : !riscv.reg):
  // CHECK: "riscv_cf.return"(%{{.*}}) : (!riscv.reg) -> ()

  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<i64 (i64, ptr)>}> ({
  ^bb0(%a: i64, %p: !llvm.ptr):
    %indirect = "llvm.call"(%p, %a) <{CConv = #llvm.cconv<fastcc>}> : (!llvm.ptr, i64) -> i64
    %explicit = "llvm.call"(%indirect) <{callee = @explicit, CConv = #llvm.cconv<ccc>}> : (i64) -> i64
    %implicit = "llvm.call"(%explicit) <{callee = @implicit}> : (i64) -> i64
    %result = "llvm.call"(%p, %implicit) <{CConv = #llvm.cconv<ccc>}> : (!llvm.ptr, i64) -> i64
    "llvm.return"(%result) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "caller"
// CHECK: "riscv_cf.call"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @explicit}> : (!riscv.reg) -> !riscv.reg
// CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @implicit}> : (!riscv.reg) -> !riscv.reg
// CHECK: "riscv_cf.call"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK: "riscv_cf.return"(%{{.*}}) : (!riscv.reg) -> ()
