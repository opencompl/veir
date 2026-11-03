// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Poison is not a known branch condition, so SCCP keeps both successor edges
// executable.
"func.func"() <{sym_name = "sccp_poison_condition", function_type = () -> ()}> ({
^entry:
  // CHECK-LABEL: func.func @sccp_poison_condition
  // CHECK: %[[CONDITION:.*]] = "llvm.mlir.poison"() : () -> i1
  // CHECK-NEXT: "cf.cond_br"(%[[CONDITION]]) [^{{[0-9]+}}, ^{{[0-9]+}}]
  %condition = "llvm.mlir.poison"() : () -> i1
  "cf.cond_br"(%condition) [^true, ^false]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^true:
  "func.return"() : () -> ()
^false:
  "func.return"() : () -> ()
}) : () -> ()
