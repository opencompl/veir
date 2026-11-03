// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "caller", function_type = () -> ()}> ({
    // CHECK: function.call: callee '@missing' does not name a function.def
    "function.call"() <{callee = @missing, mapOpGroupSizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
