// RUN: veir-interpret %s | filecheck %s --check-prefix=ANYEXT
// RUN: veir-opt %s --print-op-generic -p=legalize-riscv64,isel-riscv64,reconcile-cast,riscv-combine,dce > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=ISEL

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i64, i64, i64, i64)}> ({
    // Deliberately unrelated upper words; even the shift amount has high bits set.
    %x = "gmir.g_constant"() <{value = 0x12345678fffffffe : i64}> : () -> i64
    %two = "gmir.g_constant"() <{value = 0x7654321000000002 : i64}> : () -> i64
    %one = "gmir.g_constant"() <{value = 0x7654321000000001 : i64}> : () -> i64
    %add = "gmir.g_addw"(%x, %two) : (i64, i64) -> i64
    %sub = "gmir.g_subw"(%x, %two) : (i64, i64) -> i64
    %mul = "gmir.g_mulw"(%x, %two) : (i64, i64) -> i64
    %sdiv = "gmir.g_sdivw"(%x, %two) <{isExact}> : (i64, i64) -> i64
    %udiv = "gmir.g_udivw"(%x, %one) <{isExact}> : (i64, i64) -> i64
    %urem = "gmir.g_uremw"(%x, %two) : (i64, i64) -> i64
    %shl = "gmir.g_shlw"(%x, %one) : (i64, i64) -> i64
    %lshr = "gmir.g_lshrw"(%x, %one) <{isExact}> : (i64, i64) -> i64
    %ashr = "gmir.g_ashrw"(%x, %one) <{isExact}> : (i64, i64) -> i64
    "func.return"(%add, %sub, %mul, %sdiv, %udiv, %urem, %shl, %lshr, %ashr) : (i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// The deterministic interpreter chooses zero for unspecified high bits. Instruction
// selection chooses sign extension, which is another valid any-extension.
// ANYEXT: Program output: #[0x0000000000000000#64, 0x00000000fffffffc#64, 0x00000000fffffffc#64, 0x00000000ffffffff#64, 0x00000000fffffffe#64, 0x0000000000000000#64, 0x00000000fffffffc#64, 0x000000007fffffff#64, 0x00000000ffffffff#64]
// ISEL: Program output: #[0x0000000000000000#64, 0xfffffffffffffffc#64, 0xfffffffffffffffc#64, 0xffffffffffffffff#64, 0xfffffffffffffffe#64, 0x0000000000000000#64, 0xfffffffffffffffc#64, 0x000000007fffffff#64, 0xffffffffffffffff#64]
