// RUN: veir-opt %s -p=simplifycfg | filecheck %s

"builtin.module"() ({
  "cir.func"() <{sym_name = "cir", function_type = !cir.func<(!cir.bool, !cir.int<s, 32>) -> !cir.int<s, 32>>}> ({
  ^entry(%cond : !cir.bool, %a : !cir.int<s, 32>):
    "cir.brcond"(%cond, %a) [^empty, ^exit] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (!cir.bool, !cir.int<s, 32>) -> ()
  ^empty(%x : !cir.int<s, 32>):
    "cir.br"() [^exit] : () -> ()
  ^exit:
    "cir.return"(%a) : (!cir.int<s, 32>) -> ()
  }) : () -> ()

  // Both one- and two-operand RISC-V conditions keep their fixed operands.
  "llvm.func"() <{sym_name = "riscv", function_type = !llvm.func<i32 (i32, i32)>}> ({
  ^entry(%a : i32, %b : i32):
    "riscv_cf.beq"(%a, %b, %a, %b) [^empty, ^other] <{operandSegmentSizes = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
  ^empty(%x : i32):
    "riscv_cf.branch"(%x, %a) [^exit] : (i32, i32) -> ()
  ^other(%y : i32):
    "riscv_cf.bnez"(%y, %b, %a, %b) [^empty, ^exit] <{operandSegmentSizes = array<i32: 1, 1, 2>}> : (i32, i32, i32, i32) -> ()
  ^exit(%p : i32, %q : i32):
    "llvm.return"(%p) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "cir"
// CHECK: ^{{.*}}(%[[COND:[a-zA-Z0-9_]+]] : !cir.bool, %{{.*}} : !cir.int<s, 32>):
// CHECK-NEXT: "cir.brcond"(%[[COND]]) [^[[CIR_EXIT:[0-9]+]], ^[[CIR_EXIT]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}>
// CHECK: ^[[CIR_EXIT]]():
// CHECK-NEXT: "cir.return"

// CHECK-LABEL: "sym_name" = "riscv"
// CHECK: ^{{.*}}(%[[A:[a-zA-Z0-9_]+]] : i32, %[[B:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT: "riscv_cf.beq"(%[[A]], %[[B]], %[[A]], %[[A]], %[[B]]) [^[[EXIT:[0-9]+]], ^[[OTHER:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 1, 2, 1>}>
// CHECK: ^[[OTHER]](%[[Y:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT: "riscv_cf.bnez"(%[[Y]], %[[B]], %[[A]], %[[A]], %[[B]]) [^[[EXIT]], ^[[EXIT]]] <{"operandSegmentSizes" = array<i32: 1, 2, 2>}>
// CHECK-NEXT: ^[[EXIT]](
// CHECK-NEXT: "llvm.return"
