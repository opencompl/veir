// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "caller", function_type = () -> ()}> ({
    // CHECK: function.call: nested callee '@S::@compute' is unsupported
    "function.call"() <{callee = @S::@compute, mapOpGroupSizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
