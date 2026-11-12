// RUN: veir-opt %s -p=riscv-strict | filecheck %s

// The `riscv-strict` group is the `riscv` pipeline with every pass in its strict
// mode, which only applies the rewrites proved to refine the module.

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
    ^bb(%a: i64, %b: i64):
        %add = "llvm.add"(%a, %b) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%add) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
