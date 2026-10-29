// RUN: veir-interpret %s | filecheck %s

// Division UB is determined by the low words.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %a = "gmir.g_constant"() <{value = 0x1234567880000000 : i64}> : () -> i64
    %b = "gmir.g_constant"() <{value = 0x76543210ffffffff : i64}> : () -> i64
    %r = "gmir.g_sdivw"(%a, %b) : (i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
