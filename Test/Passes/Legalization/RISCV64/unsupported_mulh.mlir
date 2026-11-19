// RUN: not veir-opt --split-input-file %s -p=legalize-riscv64 2>&1 | filecheck %s

// The lowering of a multiply-high runs at every width, into a multiply of
// twice the width. For `i53` that multiply is `i106`, which would have to be
// narrowed back into 64-bit pieces, and narrowing is not implemented, so the
// double-width operations are where legalization stops, for the signed and the
// unsigned form alike. Which of them is reported depends on the order they are
// reached in.

"builtin.module"() ({
  "func.func"() <{function_type = (i53) -> (), sym_name = "main"}> ({
  ^bb0(%x: i53):
    %smulh = "gmir.g_smulh"(%x, %x) : (i53, i53) -> i53
    "test.test"(%smulh) : (i53) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: unable to legalize gmir.{{.*}}: no legalization rule matches

// -----

"builtin.module"() ({
  "func.func"() <{function_type = (i53) -> (), sym_name = "main"}> ({
  ^bb0(%x: i53):
    %umulh = "gmir.g_umulh"(%x, %x) : (i53, i53) -> i53
    "test.test"(%umulh) : (i53) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: unable to legalize gmir.{{.*}}: no legalization rule matches
