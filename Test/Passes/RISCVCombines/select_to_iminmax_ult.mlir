// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(X ult Y) ? X : Y` folds to `llvm.intr.umin X Y`. The compared operands
// must be exactly the select's true/false values.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %c = "llvm.icmp"(%x, %y) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %r = "llvm.select"(%c, %x, %y) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the compared operands don't match the select operands.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %c = "llvm.icmp"(%x, %y) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %r = "llvm.select"(%c, %x, %z) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The select+icmp collapse into a single umin intrinsic.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK:      %[[M:.*]] = "llvm.intr.umin"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[M]]) : (i64) -> ()

// Mismatched operands: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NZ:.*]] : i64):
// CHECK:      %[[NS:.*]] = "llvm.select"(
// CHECK:      "func.return"(%[[NS]]) : (i64) -> ()
