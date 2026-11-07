// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void (i128)>}> ({
  ^bb0(%x : i128):
    "gmir.g_br"(%x) [^bb1] : (i128) -> ()
  ^bb1(%a : i128):
    "test.test"(%a) : (i128) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// TODO: Narrow block arguments.
// CHECK: unable to legalize a block argument of type i128: narrowing type group 0 is not implemented
