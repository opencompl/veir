// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (index, index)}> ({
    %0 = "arith.constant"() <{ "value" = 42 : index }> : () -> index
    %1 = "arith.constant"() <{ "value" = -1 : index }> : () -> index
    "func.return"(%0, %1) : (index, index) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64, 0xffffffffffffffff#64]
