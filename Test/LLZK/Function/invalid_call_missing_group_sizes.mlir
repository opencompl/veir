// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = () -> ()}> ({
    // CHECK: function.call: missing 'mapOpGroupSizes' property
    "function.call"() <{callee = @bad, operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
