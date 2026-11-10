// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void (ptr)>}> ({
  ^bb0(%p: !llvm.ptr):
    %x = "gmir.g_load"(%p) <{alignment = 2 : i64, size = 32 : i64}> : (!llvm.ptr) -> i32
    "test.test"(%x) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// TODO: Lower misaligned loads, as LLVM's `lowerLoad`.
// CHECK: unable to legalize gmir.g_load: no legalization rule matches
