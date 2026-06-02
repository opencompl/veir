fastNTT:
        addi    sp, sp, -272
        sd      ra, 264(sp)
        sd      s0, 256(sp)
        addi    s0, sp, 272
        sd      a0, 176(sp)
        sd      a1, 168(sp)
        sd      a2, 160(sp)
        sd      a3, 152(sp)
        sd      a4, 144(sp)
        sd      a5, 136(sp)
        ld      a0, 144(sp)
        beqz    a0, .LBB0_2
        j       .LBB0_1
.LBB0_1:
        ld      a0, 168(sp)
        sd      a0, 40(sp)
        j       .LBB0_3
.LBB0_2:
        li      a0, 2
        sd      a0, 40(sp)
        j       .LBB0_3
.LBB0_3:
        ld      a0, 40(sp)
        sd      a0, 128(sp)
        ld      a0, 144(sp)
        beqz    a0, .LBB0_5
        j       .LBB0_4
.LBB0_4:
        li      a0, 1
        sd      a0, 32(sp)
        j       .LBB0_6
.LBB0_5:
        ld      a0, 136(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 32(sp)
        j       .LBB0_6
.LBB0_6:
        ld      a0, 32(sp)
        sd      a0, 120(sp)
        ld      a0, 168(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 112(sp)
        li      a0, 0
        sd      a0, 104(sp)
        j       .LBB0_7
.LBB0_7:
        ld      a0, 104(sp)
        sd      a0, 24(sp)
        ld      a0, 168(sp)
        sd      a0, 184(sp)
        ld      a0, 184(sp)
        sd      a0, 248(sp)
        li      a0, 0
        sd      a0, 240(sp)
        j       .LBB0_8
.LBB0_8:
        ld      a0, 248(sp)
        li      a1, 2
        blt     a0, a1, .LBB0_10
        j       .LBB0_9
.LBB0_9:
        ld      a0, 248(sp)
        srai    a0, a0, 1
        sd      a0, 248(sp)
        ld      a0, 240(sp)
        addi    a0, a0, 1
        sd      a0, 240(sp)
        j       .LBB0_8
.LBB0_10:
        ld      a0, 24(sp)
        ld      a1, 240(sp)
        bge     a0, a1, .LBB0_27
        j       .LBB0_11
.LBB0_11:
        li      a0, 0
        sd      a0, 96(sp)
        j       .LBB0_12
.LBB0_12:
        ld      a0, 96(sp)
        ld      a1, 168(sp)
        ld      a2, 128(sp)
        div     a1, a1, a2
        bge     a0, a1, .LBB0_19
        j       .LBB0_13
.LBB0_13:
        li      a0, 0
        sd      a0, 88(sp)
        j       .LBB0_14
.LBB0_14:
        ld      a0, 88(sp)
        ld      a1, 128(sp)
        srli    a2, a1, 63
        add     a1, a1, a2
        srai    a1, a1, 1
        bge     a0, a1, .LBB0_17
        j       .LBB0_15
.LBB0_15:
        ld      a0, 176(sp)
        ld      a1, 96(sp)
        ld      a2, 128(sp)
        mul     a1, a1, a2
        ld      a2, 88(sp)
        add     a1, a1, a2
        slli    a1, a1, 3
        add     a0, a0, a1
        ld      a0, 0(a0)
        sd      a0, 80(sp)
        ld      a0, 176(sp)
        ld      a1, 96(sp)
        ld      a2, 128(sp)
        mul     a1, a1, a2
        ld      a3, 88(sp)
        add     a1, a1, a3
        srli    a3, a2, 63
        add     a2, a2, a3
        srli    a2, a2, 1
        add     a1, a1, a2
        slli    a1, a1, 3
        add     a0, a0, a1
        ld      a0, 0(a0)
        sd      a0, 72(sp)
        ld      a0, 152(sp)
        ld      a1, 88(sp)
        slli    a1, a1, 1
        addi    a1, a1, 1
        ld      a2, 112(sp)
        mul     a1, a1, a2
        slli    a1, a1, 3
        add     a0, a0, a1
        ld      a0, 0(a0)
        sd      a0, 64(sp)
        ld      a3, 80(sp)
        ld      a2, 72(sp)
        ld      a1, 64(sp)
        ld      a0, 160(sp)
        sd      a3, 232(sp)
        sd      a2, 224(sp)
        sd      a1, 216(sp)
        sd      a0, 208(sp)
        addi    a0, sp, 56
        sd      a0, 200(sp)
        addi    a0, sp, 48
        sd      a0, 192(sp)
        ld      a0, 232(sp)
        ld      a1, 216(sp)
        ld      a2, 224(sp)
        mul     a2, a1, a2
        ld      a1, 208(sp)
        rem     a2, a2, a1
        add     a0, a0, a2
        rem     a0, a0, a1
        ld      a1, 200(sp)
        sd      a0, 0(a1)
        ld      a0, 232(sp)
        ld      a1, 216(sp)
        ld      a2, 224(sp)
        mul     a2, a1, a2
        ld      a1, 208(sp)
        rem     a2, a2, a1
        sub     a0, a0, a2
        add     a0, a0, a1
        rem     a0, a0, a1
        ld      a1, 192(sp)
        sd      a0, 0(a1)
        ld      a0, 56(sp)
        ld      a1, 176(sp)
        ld      a2, 96(sp)
        ld      a3, 128(sp)
        mul     a2, a2, a3
        ld      a3, 88(sp)
        add     a2, a2, a3
        slli    a2, a2, 3
        add     a1, a1, a2
        sd      a0, 0(a1)
        ld      a0, 48(sp)
        ld      a1, 176(sp)
        ld      a2, 96(sp)
        ld      a3, 128(sp)
        mul     a2, a2, a3
        ld      a4, 88(sp)
        add     a2, a2, a4
        srli    a4, a3, 63
        add     a3, a3, a4
        srli    a3, a3, 1
        add     a2, a2, a3
        slli    a2, a2, 3
        add     a1, a1, a2
        sd      a0, 0(a1)
        j       .LBB0_16
.LBB0_16:
        ld      a0, 88(sp)
        addi    a0, a0, 1
        sd      a0, 88(sp)
        j       .LBB0_14
.LBB0_17:
        j       .LBB0_18
.LBB0_18:
        ld      a0, 96(sp)
        addi    a0, a0, 1
        sd      a0, 96(sp)
        j       .LBB0_12
.LBB0_19:
        ld      a0, 112(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 112(sp)
        ld      a0, 144(sp)
        beqz    a0, .LBB0_21
        j       .LBB0_20
.LBB0_20:
        ld      a0, 128(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 16(sp)
        j       .LBB0_22
.LBB0_21:
        ld      a0, 128(sp)
        slli    a0, a0, 1
        sd      a0, 16(sp)
        j       .LBB0_22
.LBB0_22:
        ld      a0, 16(sp)
        sd      a0, 128(sp)
        ld      a0, 144(sp)
        beqz    a0, .LBB0_24
        j       .LBB0_23
.LBB0_23:
        ld      a0, 120(sp)
        slli    a0, a0, 1
        sd      a0, 8(sp)
        j       .LBB0_25
.LBB0_24:
        ld      a0, 120(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 8(sp)
        j       .LBB0_25
.LBB0_25:
        ld      a0, 8(sp)
        sd      a0, 120(sp)
        j       .LBB0_26
.LBB0_26:
        ld      a0, 104(sp)
        addi    a0, a0, 1
        sd      a0, 104(sp)
        j       .LBB0_7
.LBB0_27:
        ld      ra, 264(sp)
        ld      s0, 256(sp)
        addi    sp, sp, 272
        ret