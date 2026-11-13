// RUN: veir-opt %s -p=riscv | filecheck %s

// Unknown inputs prevent constant folding from hiding incomplete lowering.
// Any instruction sequence is fine, provided it fully lowers both comparisons.
"builtin.module"() ({
  "func.func"() <{sym_name = "cmp", function_type = (i8, i8, i64, i64) -> (i32, i2)}> ({
  ^bb0(%a: i8, %b: i8, %c: i64, %d: i64):
    %s = "llvm.intr.scmp"(%a, %b) : (i8, i8) -> i32
    %u = "llvm.intr.ucmp"(%c, %d) : (i64, i64) -> i2
    "func.return"(%s, %u) : (i32, i2) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "builtin.module"
// CHECK-NOT: "gmir
// CHECK-NOT: "llvm.intr.
