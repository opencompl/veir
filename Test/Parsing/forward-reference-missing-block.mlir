// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
  ^entry:
    "cf.br"() [^missing] : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:forward-reference-missing-block.mlir:6:16: error: block %missing was used but never defined
// CHECK-NEXT:    "cf.br"() [^missing] : () -> ()
// CHECK-NEXT:               ^
