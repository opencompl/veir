// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i256}> : () -> i256
    %add = "gmir.g_add"(%x, %x) : (i256, i256) -> i256
    "test.test"(%add) : (i256) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// TODO: Narrow to more than two parts once `g_merge_values` and `g_unmerge_values` are variadic.
// (This error is expected when a required legalization action has not been
// implemented yet.)
// CHECK: unable to legalize gmir.g_add: narrowing type group 0 is not implemented
