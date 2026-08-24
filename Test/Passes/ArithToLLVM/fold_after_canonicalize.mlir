// RUN: veir-opt %s -p=canonicalize > %t
// RUN: filecheck %s --check-prefix=AFTER-FOLDER --input-file=%t
// RUN: veir-opt %t -p=arith-to-llvm | filecheck %s --check-prefix=LOWERED

// Even after canonicalization, an operation with a mixture of known and
// unknown operands cannot fold as a whole. Lowering that operation can expose
// constant-only pieces of its expansion, which `createOrFold!` then folds.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i8) -> i8}> ({
    ^entry(%divisor : i8):
      %c255 = "arith.constant"() <{value = 255 : i8}> : () -> i8
      %result = "arith.ceildivui"(%c255, %divisor) : (i8, i8) -> i8
      "func.return"(%result) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// The folder cannot evaluate ceildivui because the divisor is unknown.
// AFTER-FOLDER: "arith.constant"
// AFTER-FOLDER: "arith.ceildivui"

// ceildivui expands to:
//   isZero = icmp 255, 0
//   adjusted = sub 255, 1
//   quotient = udiv adjusted, divisor
//   ...
// The first two expressions fold during lowering, while udiv remains because
// its divisor is still unknown.
// LOWERED: "llvm.mlir.constant"() <{"value" = 0 : i8}>
// LOWERED: "llvm.mlir.constant"() <{"value" = 1 : i8}>
// LOWERED: "llvm.mlir.constant"() <{"value" = 0 : i1}>
// LOWERED: "llvm.mlir.constant"() <{"value" = -2 : i8}>
// LOWERED-NOT: "llvm.icmp"
// LOWERED-NOT: "llvm.sub"
// LOWERED: "llvm.udiv"
