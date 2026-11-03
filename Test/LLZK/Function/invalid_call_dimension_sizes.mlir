// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = (index) -> ()}> ({
  ^entry(%arg0: index):
    // CHECK: Error verifying input program: function.call: map group 0 has 1 operand(s), fewer than its 2 dimension(s)
    "function.call"(%arg0) <{callee = @bad, mapOpGroupSizes = array<i32: 1>, numDimsPerMap = array<i32: 2>, operandSegmentSizes = array<i32: 0, 1>}> : (index) -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
