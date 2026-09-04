// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = (index) -> ()}> ({
  ^entry(%arg0: index):
    // CHECK: Error verifying input program: function.call: numDimsPerMap expected 1 entries, got 0
    "function.call"(%arg0) <{callee = @bad, mapOpGroupSizes = array<i32: 1>, operandSegmentSizes = array<i32: 0, 1>}> : (index) -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
