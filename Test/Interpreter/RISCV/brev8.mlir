// RUN: veir-interpret %s | filecheck %s
// RUN: VEIR_ROUNDTRIP --check-prefix=ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %x0 = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
    %r0 = "riscv.brev8"(%x0) : (!riscv.reg) -> !riscv.reg
    %x1 = "riscv.li"() <{value = 18446744073709551615 : i64}> : () -> !riscv.reg
    %r1 = "riscv.brev8"(%x1) : (!riscv.reg) -> !riscv.reg
    %x2 = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
    %r2 = "riscv.brev8"(%x2) : (!riscv.reg) -> !riscv.reg
    %x3 = "riscv.li"() <{value = 9223372036854775808 : i64}> : () -> !riscv.reg
    %r3 = "riscv.brev8"(%x3) : (!riscv.reg) -> !riscv.reg
    %x4 = "riscv.li"() <{value = 81985529216486895 : i64}> : () -> !riscv.reg
    %r4 = "riscv.brev8"(%x4) : (!riscv.reg) -> !riscv.reg
    %x5 = "riscv.li"() <{value = 9241421688590303745 : i64}> : () -> !riscv.reg
    %r5 = "riscv.brev8"(%x5) : (!riscv.reg) -> !riscv.reg
    %twice = "riscv.brev8"(%r4) : (!riscv.reg) -> !riscv.reg
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5, %twice) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0xffffffffffffffff#64, 0x0000000000000080#64, 0x0100000000000000#64, 0x80c4a2e691d5b3f7#64, 0x0102040810204080#64, 0x0123456789abcdef#64]
// ROUNDTRIP: "riscv.brev8"
