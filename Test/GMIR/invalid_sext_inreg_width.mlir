// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %sext_inreg = "gmir.g_sext_inreg"(%x) <{sz = 32 : i64}> : (i32) -> i32
    "test.test"(%sext_inreg) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_sext_inreg: Expected 'sz' to be smaller than the operand width 32, but got 32
