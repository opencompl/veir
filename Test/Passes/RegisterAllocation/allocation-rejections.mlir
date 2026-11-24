// RUN: not veir-opt %s -p=register-allocation-riscv64 2>&1 >/dev/null | filecheck %s

// Allocation-only rejections. The function shapes both register passes reject are in
// `unsupported-functions.mlir`.

// A function argument that is not precoloured: it would get a virtual register that the
// signature does not mention.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg) -> ()}> ({
  ^entry(%a : !riscv.reg):
    %sum = "riscv.add"(%a, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register allocation requires precoloured function arguments; run register-precolouring-riscv64 first
