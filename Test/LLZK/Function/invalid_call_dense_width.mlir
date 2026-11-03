// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: function.call: expected 'operandSegmentSizes' to be an array<i32> attribute
"builtin.module"() ({
  "function.def"() <{sym_name = "caller", function_type = () -> ()}> ({
    "function.call"() <{callee = @caller, mapOpGroupSizes = array<i32>, operandSegmentSizes = array<i64: 0, 0>}> : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
