// RUN: veir-interpret %s | filecheck %s

// A poison carry-in makes both results poison.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1)}> ({
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %carry = "llvm.mlir.poison"() : () -> i1
    %x, %x_carry = "gmir.g_uadde"(%one, %one, %carry) : (i8, i8, i1) -> (i8, i1)
    "func.return"(%x, %x_carry) : (i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, poison]
