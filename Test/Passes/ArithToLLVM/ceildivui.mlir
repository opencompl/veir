// RUN: veir-opt %s --mlir-print-op-generic -p=arith-to-llvm > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --check-prefix=LOWERED --input-file=%t

// Unsigned ceiling division at zero, exact and non-exact quotients, and the
// maximum i8 numerator/divisor boundaries.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8)}> ({
    %c0 = "arith.constant"() <{value = 0 : i8}> : () -> i8
    %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %c2 = "arith.constant"() <{value = 2 : i8}> : () -> i8
    %c254 = "arith.constant"() <{value = 254 : i8}> : () -> i8
    %c255 = "arith.constant"() <{value = 255 : i8}> : () -> i8
    %r0 = "arith.ceildivui"(%c0, %c255) : (i8, i8) -> i8
    %r1 = "arith.ceildivui"(%c1, %c255) : (i8, i8) -> i8
    %r2 = "arith.ceildivui"(%c254, %c2) : (i8, i8) -> i8
    %r3 = "arith.ceildivui"(%c255, %c2) : (i8, i8) -> i8
    %r4 = "arith.ceildivui"(%c255, %c255) : (i8, i8) -> i8
    "func.return"(%r0, %r1, %r2, %r3, %r4) : (i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x00#8, 0x01#8, 0x7f#8, 0x80#8, 0x01#8]

// LOWERED: "builtin.module"
// LOWERED-NOT: "arith.
