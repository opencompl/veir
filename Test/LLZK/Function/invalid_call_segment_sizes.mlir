// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = () -> ()}> ({
    // CHECK: Error verifying input program: function.call: operandSegmentSizes describes 1 operands, got 0
    "function.call"() <{callee = @bad, mapOpGroupSizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
