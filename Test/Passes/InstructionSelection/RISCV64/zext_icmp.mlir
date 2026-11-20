// RUN: veir-opt %s -p=riscv | filecheck %s

// A zero extension of an `icmp` result needs no `andi`: `slt`/`sltu` already
// produce 0 or 1, and the post-legalizer combiner drops the redundant `g_and`.
// Each `icmp` also feeds a `sext`, so the `andi` cannot be folded into the only
// user of the comparison.

"builtin.module"() ({
    "func.func"() <{function_type = (i64, i64) -> (i64, i64, i32, i32), sym_name = "zext_icmp"}> ({
    ^bb0(%a: i64, %b: i64):
        %c = "llvm.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        %z64 = "llvm.zext"(%c) : (i1) -> i64
        %s64 = "llvm.sext"(%c) : (i1) -> i64
        %d = "llvm.icmp"(%a, %b) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
        %z32 = "llvm.zext"(%d) : (i1) -> i32
        %s32 = "llvm.sext"(%d) : (i1) -> i32
        "func.return"(%z64, %s64, %z32, %s32) : (i64, i64, i32, i32) -> ()
    }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @zext_icmp
// CHECK-NOT:   "riscv.andi"
// CHECK:       "func.return"
