// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// llvm.mlir.global is isolated from above, so its initializer may not capture
// an SSA value from the module body.

"builtin.module"() ({
  %v = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g"}> ({
    "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.return: operand uses a value defined outside the isolated region
