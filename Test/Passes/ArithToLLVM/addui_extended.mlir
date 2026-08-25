// RUN: veir-opt %s --mlir-print-op-generic -p=arith-to-llvm > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --check-prefix=LOWERED --input-file=%t

// Exercise both results around the i8 carry boundary:
//   0 + 0       = 0x00, carry 0
//   255 + 0     = 0xff, carry 0
//   255 + 1     = 0x00, carry 1
//   128 + 128   = 0x00, carry 1
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1, i8, i1, i8, i1)}> ({
    %c0 = "arith.constant"() <{value = 0 : i8}> : () -> i8
    %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %c128 = "arith.constant"() <{value = 128 : i8}> : () -> i8
    %c255 = "arith.constant"() <{value = 255 : i8}> : () -> i8
    %s0, %o0 = "arith.addui_extended"(%c0, %c0) : (i8, i8) -> (i8, i1)
    %s1, %o1 = "arith.addui_extended"(%c255, %c0) : (i8, i8) -> (i8, i1)
    %s2, %o2 = "arith.addui_extended"(%c255, %c1) : (i8, i8) -> (i8, i1)
    %s3, %o3 = "arith.addui_extended"(%c128, %c128) : (i8, i8) -> (i8, i1)
    "func.return"(%s0, %o0, %s1, %o1, %s2, %o2, %s3, %o3)
      : (i8, i1, i8, i1, i8, i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x00#8, 0x0#1, 0xff#8, 0x0#1, 0x00#8, 0x1#1, 0x00#8, 0x1#1]

// LOWERED: "builtin.module"
// LOWERED-NOT: "arith.
