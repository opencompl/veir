// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// Division by a constant power of two (LLVM's `intdiv_combines`), on the `gmir` divisions and on
// the RISC-V word divisions, which read only the low 32 bits of the divisor.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
    // CHECK:     %[[X:.*]] = "test.test"() : () -> i64
    %x = "test.test"() : () -> i64
    %c1 = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %cm1 = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %cmin = "gmir.g_constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %cm16 = "gmir.g_constant"() <{value = -16 : i64}> : () -> i64
    %c6 = "gmir.g_constant"() <{value = 6 : i64}> : () -> i64
    %w31 = "gmir.g_constant"() <{value = 2147483648 : i64}> : () -> i64
    %wmin = "gmir.g_constant"() <{value = -2147483648 : i64}> : () -> i64
    %hi = "gmir.g_constant"() <{value = 4294967300 : i64}> : () -> i64

    // `sdiv x, 1` -> `x`, and `sdiv x, -1` -> `0 - x`.
    // CHECK:      %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
    // CHECK-NEXT: %[[NEGX:.*]] = "gmir.g_sub"(%[[ZERO]], %[[X]])
    %a = "gmir.g_sdiv"(%x, %c1) : (i64, i64) -> i64
    %b = "gmir.g_sdiv"(%x, %cm1) : (i64, i64) -> i64

    // `sdiv x, INT64_MIN`: the bias-and-shift sequence with `k = 63`, negated.
    // CHECK-NEXT: %[[C63:.*]] = "gmir.g_constant"() <{"value" = 63 : i64}>
    // CHECK-NEXT: %[[SIGN:.*]] = "gmir.g_ashr"(%[[X]], %[[C63]])
    // CHECK-NEXT: %[[C1:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}>
    // CHECK-NEXT: %[[BIAS:.*]] = "gmir.g_lshr"(%[[SIGN]], %[[C1]])
    // CHECK-NEXT: %[[SUM:.*]] = "gmir.g_add"(%[[X]], %[[BIAS]])
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 63 : i64}>
    // CHECK-NEXT: %[[Q:.*]] = "gmir.g_ashr"(%[[SUM]], %[[K]])
    // CHECK-NEXT: %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
    // CHECK-NEXT: %[[MINQ:.*]] = "gmir.g_sub"(%[[Z]], %[[Q]])
    %c = "gmir.g_sdiv"(%x, %cmin) : (i64, i64) -> i64

    // `sdiv exact x, -16` -> `0 - (ashr exact x, 4)`.
    // CHECK-NEXT: %[[C4:.*]] = "gmir.g_constant"() <{"value" = 4 : i64}>
    // CHECK-NEXT: %[[SHR:.*]] = "gmir.g_ashr"(%[[X]], %[[C4]]) <{isExact}>
    // CHECK-NEXT: %[[Z2:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
    // CHECK-NEXT: %[[EXACT:.*]] = "gmir.g_sub"(%[[Z2]], %[[SHR]])
    %d = "gmir.g_sdiv"(%x, %cm16) <{isExact}> : (i64, i64) -> i64

    // Not a power of two: unchanged.
    // CHECK-NEXT: %[[SDIV6:.*]] = "gmir.g_sdiv"(%[[X]], %{{.*}})
    %e = "gmir.g_sdiv"(%x, %c6) : (i64, i64) -> i64

    // `udiv x, 2^63`: the divisor is read as unsigned.
    // CHECK-NEXT: %[[C63B:.*]] = "gmir.g_constant"() <{"value" = 63 : i64}>
    // CHECK-NEXT: %[[UMIN:.*]] = "gmir.g_lshr"(%[[X]], %[[C63B]])
    %f = "gmir.g_udiv"(%x, %cmin) : (i64, i64) -> i64

    // `divuw x, 2^31` -> `srlw x, 31`.
    // CHECK-NEXT: %[[C31:.*]] = "gmir.g_constant"() <{"value" = 31 : i64}>
    // CHECK-NEXT: %[[WU:.*]] = "gmir_riscv.g_srlw"(%[[X]], %[[C31]])
    %g = "gmir_riscv.g_divuw"(%x, %w31) : (i64, i64) -> i64

    // `divw x, INT32_MIN`: the word sequence with `k = 31`, negated.
    // CHECK-NEXT: %[[W31:.*]] = "gmir.g_constant"() <{"value" = 31 : i64}>
    // CHECK-NEXT: %[[WSIGN:.*]] = "gmir_riscv.g_sraw"(%[[X]], %[[W31]])
    // CHECK-NEXT: %[[W1:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}>
    // CHECK-NEXT: %[[WBIAS:.*]] = "gmir_riscv.g_srlw"(%[[WSIGN]], %[[W1]])
    // CHECK-NEXT: %[[WSUM:.*]] = "gmir_riscv.g_addw"(%[[X]], %[[WBIAS]])
    // CHECK-NEXT: %[[WK:.*]] = "gmir.g_constant"() <{"value" = 31 : i64}>
    // CHECK-NEXT: %[[WQ:.*]] = "gmir_riscv.g_sraw"(%[[WSUM]], %[[WK]])
    // CHECK-NEXT: %[[WZ:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
    // CHECK-NEXT: %[[WMIN:.*]] = "gmir_riscv.g_subw"(%[[WZ]], %[[WQ]])
    %h = "gmir_riscv.g_divw"(%x, %wmin) : (i64, i64) -> i64

    // `divw x, -16`: only the low 32 bits of the divisor count.
    // CHECK:      %[[C28:.*]] = "gmir.g_constant"() <{"value" = 28 : i64}>
    // CHECK-NEXT: "gmir_riscv.g_srlw"(%{{.*}}, %[[C28]])
    // CHECK:      %[[WNEG16:.*]] = "gmir_riscv.g_subw"
    %i = "gmir_riscv.g_divw"(%x, %cm16) : (i64, i64) -> i64

    // `divw x, 1` is left alone: `x` is not sign-extended from 32 bits.
    // CHECK-NEXT: %[[DIVW1:.*]] = "gmir_riscv.g_divw"(%[[X]], %{{.*}})
    %j = "gmir_riscv.g_divw"(%x, %c1) : (i64, i64) -> i64

    // `divuw x, 2^32 + 4` reads the divisor as `4`.
    // CHECK-NEXT: %[[C2:.*]] = "gmir.g_constant"() <{"value" = 2 : i64}>
    // CHECK-NEXT: %[[WHI:.*]] = "gmir_riscv.g_srlw"(%[[X]], %[[C2]])
    %k = "gmir_riscv.g_divuw"(%x, %hi) : (i64, i64) -> i64

    // `divw exact x, -16` -> `0 - (sraw x, 4)`, and `divw exact x, 1` -> `sraw x, 0`.
    // CHECK-NEXT: %[[WC4:.*]] = "gmir.g_constant"() <{"value" = 4 : i64}>
    // CHECK-NEXT: %[[WSHR:.*]] = "gmir_riscv.g_sraw"(%[[X]], %[[WC4]])
    // CHECK-NEXT: %[[WZ3:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
    // CHECK-NEXT: %[[WEXACT:.*]] = "gmir_riscv.g_subw"(%[[WZ3]], %[[WSHR]])
    %m = "gmir_riscv.g_divw"(%x, %cm16) <{isExact}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[WC0:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
    // CHECK-NEXT: %[[WEXACT1:.*]] = "gmir_riscv.g_sraw"(%[[X]], %[[WC0]])
    %n = "gmir_riscv.g_divw"(%x, %c1) <{isExact}> : (i64, i64) -> i64

    // CHECK-NEXT: "test.test"(%[[X]], %[[NEGX]], %[[MINQ]], %[[EXACT]], %[[SDIV6]], %[[UMIN]], %[[WU]], %[[WMIN]], %[[WNEG16]], %[[DIVW1]], %[[WHI]], %[[WEXACT]], %[[WEXACT1]])
    "test.test"(%a, %b, %c, %d, %e, %f, %g, %h, %i, %j, %k, %m, %n) : (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
