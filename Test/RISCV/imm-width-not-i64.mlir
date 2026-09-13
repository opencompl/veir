// RUN: not veir-opt %s 2>&1 | filecheck %s

// The RISC-V dialects are ours alone, so -- unlike `llvm.mlir.constant`, which
// must let the value attribute's width differ from the result width for upstream
// compatibility -- a RISC-V immediate must be declared at the width a register
// holds. `RISCVImmediateProperties.value` is a `BitVec 64`, so the only place a
// disagreeing width can enter is the parse boundary, which rejects it here.
//
// `3 : i6` is what this shift amount used to be spelled as. Note that 63, the
// largest legal `uimm6`, is not even representable as a *signed* i6, which is
// why the immediate's own encoding field is the wrong width to declare.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    %b = "riscv.slli"(%a) <{ "value" = 3 : i6 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%b) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: RISC-V immediate operation: expected 'value' to be a 64-bit signless integer attribute, but got i6
