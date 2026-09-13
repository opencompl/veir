// RUN: not veir-opt %s 2>&1 | filecheck %s

// 7 does *not* fit into i2. The modulus is an attribute of the storage type,
// so the literal is rejected where every other out-of-range literal is, when
// the attribute is parsed, rather than later by the type's verifier.
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<7 : i2>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 1 : i2}> : () -> !mod_arith.int<7 : i2>
      "func.return"(%0) : (!mod_arith.int<7 : i2>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: integer constant out of range for attribute
