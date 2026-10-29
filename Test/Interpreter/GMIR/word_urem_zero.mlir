// RUN: veir-interpret %s | filecheck %s

// Division UB is determined by the low words.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %a = "gmir.g_constant"() <{value = 42 : i64}> : () -> i64
    %b = "gmir.g_constant"() <{value = 0x7654321000000000 : i64}> : () -> i64
    %r = "gmir.g_uremw"(%a, %b) : (i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
