// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "target", function_type = (index) -> index}> ({
  ^entry(%x : index):
    "function.return"(%x) : (index) -> ()
  }) : () -> ()
  "function.def"() <{sym_name = "caller", function_type = (!felt.type) -> ()}> ({
  ^entry(%x : !felt.type):
    // CHECK: function.call: operand 0 type does not match the callee's input type
    "function.call"(%x) <{callee = @target, mapOpGroupSizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!felt.type) -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
