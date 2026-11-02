// RUN: veir-opt %s -p=riscv > %t.mlir
// RUN: not veir2mir %t.mlir > %t.out 2> %t.err
// RUN: filecheck %s --input-file=%t.err
// RUN: test ! -s %t.out

// A function whose boundary has a type that is not passed in a single register
// is left unlowered by isel-abi-riscv64, and veir2mir rejects it rather than
// printing its `llvm.return` as a return.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "ret_sext_i17", function_type = !llvm.func<i17 (i17)>, res_attrs = [{llvm.signext}]}> ({
  ^bb0(%x: i17):
    "llvm.return"(%x) : (i17) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2mir: error: function @ret_sext_i17: argument of unlowered type i17
