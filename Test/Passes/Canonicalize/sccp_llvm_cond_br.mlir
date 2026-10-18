// RUN: veir-opt %s -p=canonicalize | filecheck %s

// SCCP uses the control flow interface for LLVM branches. A false condition
// leaves the false successor executable and propagates its block argument, and
// the branch becomes an unconditional branch to the false successor.
"func.func"() <{sym_name = "sccp_llvm_cond_br", function_type = () -> i32}> ({
^entry:
  %condition = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
  "llvm.cond_br"(%condition) [^true, ^false]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^true:
  %one = "arith.constant"() <{value = 1 : i32}> : () -> i32
  "cf.br"(%one) [^join] : (i32) -> ()
^false:
  %two = "arith.constant"() <{value = 2 : i32}> : () -> i32
  "cf.br"(%two) [^join] : (i32) -> ()
^join(%result : i32):
  // CHECK-LABEL: func.func @sccp_llvm_cond_br
  // CHECK:      %[[TWO:.*]] = "arith.constant"() <{"value" = 2 : i32}>
  // CHECK-NEXT: "llvm.br"() [^[[FALSE:[0-9]+]]] : () -> ()
  // CHECK:      ^[[FALSE]]():
  // CHECK-NEXT: "cf.br"(%[[TWO]])
  // CHECK:      "func.return"(%[[TWO]]) : (i32) -> ()
  "func.return"(%result) : (i32) -> ()
}) : () -> ()
