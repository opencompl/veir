// RUN: veir-opt %s --mlir-print-op-generic -p=arith-to-llvm > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --check-prefix=LOWERED --input-file=%t

// Check low/high halves for negative products and signed i8 endpoints:
//   -128 * 2    = 0xff00
//   -128 * -1   = 0x0080
//    127 * 127  = 0x3f01
//   -128 * -128 = 0x4000
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8, i8, i8)}> ({
    %cn128 = "arith.constant"() <{value = -128 : i8}> : () -> i8
    %cn1 = "arith.constant"() <{value = -1 : i8}> : () -> i8
    %c2 = "arith.constant"() <{value = 2 : i8}> : () -> i8
    %c127 = "arith.constant"() <{value = 127 : i8}> : () -> i8
    %lo0, %hi0 = "arith.mulsi_extended"(%cn128, %c2) : (i8, i8) -> (i8, i8)
    %lo1, %hi1 = "arith.mulsi_extended"(%cn128, %cn1) : (i8, i8) -> (i8, i8)
    %lo2, %hi2 = "arith.mulsi_extended"(%c127, %c127) : (i8, i8) -> (i8, i8)
    %lo3, %hi3 = "arith.mulsi_extended"(%cn128, %cn128) : (i8, i8) -> (i8, i8)
    "func.return"(%lo0, %hi0, %lo1, %hi1, %lo2, %hi2, %lo3, %hi3)
      : (i8, i8, i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x00#8, 0xff#8, 0x80#8, 0x00#8, 0x01#8, 0x3f#8, 0x00#8, 0x40#8]

// LOWERED: "builtin.module"
// LOWERED-NOT: "arith.
