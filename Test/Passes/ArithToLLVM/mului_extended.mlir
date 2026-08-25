// RUN: veir-opt %s --mlir-print-op-generic -p=arith-to-llvm > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --check-prefix=LOWERED --input-file=%t

// Check low/high halves at unsigned i8 boundaries:
//   0 * 255     = 0x0000
//   255 * 1     = 0x00ff
//   128 * 2     = 0x0100
//   255 * 255   = 0xfe01
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8, i8, i8)}> ({
    %c0 = "arith.constant"() <{value = 0 : i8}> : () -> i8
    %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %c2 = "arith.constant"() <{value = 2 : i8}> : () -> i8
    %c128 = "arith.constant"() <{value = 128 : i8}> : () -> i8
    %c255 = "arith.constant"() <{value = 255 : i8}> : () -> i8
    %lo0, %hi0 = "arith.mului_extended"(%c0, %c255) : (i8, i8) -> (i8, i8)
    %lo1, %hi1 = "arith.mului_extended"(%c255, %c1) : (i8, i8) -> (i8, i8)
    %lo2, %hi2 = "arith.mului_extended"(%c128, %c2) : (i8, i8) -> (i8, i8)
    %lo3, %hi3 = "arith.mului_extended"(%c255, %c255) : (i8, i8) -> (i8, i8)
    "func.return"(%lo0, %hi0, %lo1, %hi1, %lo2, %hi2, %lo3, %hi3)
      : (i8, i8, i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x00#8, 0x00#8, 0xff#8, 0x00#8, 0x00#8, 0x01#8, 0x01#8, 0xfe#8]

// LOWERED: "builtin.module"
// LOWERED-NOT: "arith.
