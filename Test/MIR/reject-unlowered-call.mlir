// RUN: veir-opt %s -p=riscv > %t.mlir
// RUN: not veir2mir %t.mlir > %t.out 2> %t.err
// RUN: filecheck %s --input-file=%t.err
// RUN: test ! -s %t.out

// The caller's own boundary is lowered, but its call to a function taking an
// `i17` is not; veir2mir must reject it rather than drop the call.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "take_i17", function_type = !llvm.func<void (i17)>, arg_attrs = [{llvm.signext}]}> ({
  }) : () -> ()
  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<void (i64)>}> ({
  ^bb0(%a: i64):
    %t = "llvm.trunc"(%a) : (i64) -> i17
    "llvm.call"(%t) <{callee = @take_i17}> : (i17) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2mir: error: function @caller: unlowered operation '{{builtin.unrealized_conversion_cast|llvm.call}}'
