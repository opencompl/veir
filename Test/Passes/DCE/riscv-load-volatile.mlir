// RUN: veir-opt %s -p=dce | filecheck %s

// An unused ordinary load can be removed, but an unused volatile load is
// side-effecting and must remain.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (), sym_name = "main"}> ({
  ^bb0(%addr: !riscv.reg):
    %plain = "riscv.ld"(%addr) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %volatile = "riscv.ld"(%addr) <{"value" = 8 : i64, volatile_}> : (!riscv.reg) -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @main(%{{.*}}: !riscv.reg) {
// CHECK-NOT: "riscv.ld"({{.*}}) <{"value" = 0 : i64}>
// CHECK: %{{.*}} = "riscv.ld"(%{{.*}}) <{"value" = 8 : i64, volatile_}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"() : () -> ()
