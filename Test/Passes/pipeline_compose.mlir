// RUN: veir-opt %s -p=canonicalize -p=riscv,cse -p=dce | filecheck %s

// Check that repeated -p flags build one pipeline in the order the flags appear
// on the command line, and that a pass-group name inside a -p list expands in
// place to the group's passes.

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> i64}> ({
    ^bb(%a: i64, %b: i64):
        %add = "llvm.add"(%a, %b) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%add) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
