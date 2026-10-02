// RUN: VEIR_ROUNDTRIP
// RUN: veir-opt %s --print-op-generic -p=dce,cse,dce | filecheck %s
//
// Calls have register operands/results, may return multiple values, and are
// not terminators. Even identical calls with unused results must survive CSE
// and DCE. Direct symbols may name external functions.

"builtin.module"() ({
  "func.func"() <{sym_name = "caller", function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg)}> ({
  ^entry(%target: !riscv.reg, %arg: !riscv.reg):
    %unused0 = "riscv_cf.call"(%arg) <{callee = @external}> : (!riscv.reg) -> !riscv.reg
    %unused1 = "riscv_cf.call"(%arg) <{callee = @external}> : (!riscv.reg) -> !riscv.reg
    %first, %second = "riscv_cf.call"(%target, %arg) : (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg)
    "riscv_cf.call"() <{callee = @external_void}> : () -> ()
    "riscv_cf.call"(%target) : (!riscv.reg) -> ()
    "riscv_cf.return"(%first, %second) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "void_func", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "llvm_identity", function_type = !llvm.func<!riscv.reg (!riscv.reg)>}> ({
  ^entry(%arg: !riscv.reg):
    %result = "riscv_cf.call"(%arg) <{callee = @llvm_identity}> : (!riscv.reg) -> !riscv.reg
    "riscv_cf.return"(%result) : (!riscv.reg) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "llvm_void", function_type = !llvm.func<void ()>}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %{{.*}} = "riscv_cf.call"(%{{.*}}) <{"callee" = @external}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv_cf.call"(%{{.*}}) <{"callee" = @external}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}}:2 = "riscv_cf.call"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg)
// CHECK-NEXT: "riscv_cf.call"() <{"callee" = @external_void}> : () -> ()
// CHECK-NEXT: "riscv_cf.call"(%{{.*}}) : (!riscv.reg) -> ()
// CHECK-NEXT: "riscv_cf.return"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> ()
// CHECK:      "riscv_cf.return"() : () -> ()
// CHECK:      "riscv_cf.call"(%{{.*}}) <{"callee" = @llvm_identity}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "riscv_cf.return"(%{{.*}}) : (!riscv.reg) -> ()
// CHECK:      "riscv_cf.return"() : () -> ()
