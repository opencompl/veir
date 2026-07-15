// RUN: veir-opt %s -p=canonicalize,print-ir -p=riscv,print-ir -p=cse -p=dce 2>&1 | filecheck %s

// Check that repeated -p flags build one pipeline in the order the flags appear
// on the command line, and that a pass-group name inside a -p list expands in
// place to the group's passes. The print-ir probes (which dump to stderr) witness
// the order: the dump after the first flag must still contain llvm.add, and the
// dump after the riscv group must contain riscv.add.

// CHECK: IR Dump
// CHECK: "llvm.add"
// CHECK: IR Dump
// CHECK: "riscv.add"

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> i64}> ({
    ^bb(%a: i64, %b: i64):
        %add = "llvm.add"(%a, %b) : (i64, i64) -> i64
        "func.return"(%add) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
