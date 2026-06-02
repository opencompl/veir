log2FloorAux:
        addi    sp, sp, -32
        sd      ra, 24(sp)
        sd      s0, 16(sp)
        addi    s0, sp, 32
        sd      a0, 8(sp)
        li      a0, 0
        sd      a0, 0(sp)
        j       .LBB0_1
.LBB0_1:
        ld      a0, 8(sp)
        li      a1, 2
        blt     a0, a1, .LBB0_3
        j       .LBB0_2
.LBB0_2:
        ld      a0, 8(sp)
        srai    a0, a0, 1
        sd      a0, 8(sp)
        ld      a0, 0(sp)
        addi    a0, a0, 1
        sd      a0, 0(sp)
        j       .LBB0_1
.LBB0_3:
        ld      a0, 0(sp)
        ld      ra, 24(sp)
        ld      s0, 16(sp)
        addi    sp, sp, 32
        ret

log2Floor:
        addi    sp, sp, -48
        sd      ra, 40(sp)
        sd      s0, 32(sp)
        addi    s0, sp, 48
        sd      a0, 8(sp)
        ld      a0, 8(sp)
        sd      a0, 24(sp)
        li      a0, 0
        sd      a0, 16(sp)
        j       .LBB1_1
.LBB1_1:
        ld      a0, 24(sp)
        li      a1, 2
        blt     a0, a1, .LBB1_3
        j       .LBB1_2
.LBB1_2:
        ld      a0, 24(sp)
        srai    a0, a0, 1
        sd      a0, 24(sp)
        ld      a0, 16(sp)
        addi    a0, a0, 1
        sd      a0, 16(sp)
        j       .LBB1_1
.LBB1_3:
        ld      a0, 16(sp)
        ld      ra, 40(sp)
        ld      s0, 32(sp)
        addi    sp, sp, 48
        ret

bflyCT:
        addi    sp, sp, -64
        sd      ra, 56(sp)
        sd      s0, 48(sp)
        addi    s0, sp, 64
        sd      a0, 40(sp)
        sd      a1, 32(sp)
        sd      a2, 24(sp)
        sd      a3, 16(sp)
        sd      a4, 8(sp)
        sd      a5, 0(sp)
        ld      a0, 40(sp)
        ld      a1, 24(sp)
        ld      a2, 32(sp)
        mul     a2, a1, a2
        ld      a1, 16(sp)
        rem     a2, a2, a1
        add     a0, a0, a2
        rem     a0, a0, a1
        ld      a1, 8(sp)
        sd      a0, 0(a1)
        ld      a0, 40(sp)
        ld      a1, 24(sp)
        ld      a2, 32(sp)
        mul     a2, a1, a2
        ld      a1, 16(sp)
        rem     a2, a2, a1
        sub     a0, a0, a2
        add     a0, a0, a1
        rem     a0, a0, a1
        ld      a1, 0(sp)
        sd      a0, 0(a1)
        ld      ra, 56(sp)
        ld      s0, 48(sp)
        addi    sp, sp, 64
        ret

bflyGS:
        addi    sp, sp, -64
        sd      ra, 56(sp)
        sd      s0, 48(sp)
        addi    s0, sp, 64
        sd      a0, 40(sp)
        sd      a1, 32(sp)
        sd      a2, 24(sp)
        sd      a3, 16(sp)
        sd      a4, 8(sp)
        sd      a5, 0(sp)
        ld      a0, 40(sp)
        ld      a1, 32(sp)
        add     a0, a0, a1
        ld      a1, 16(sp)
        rem     a0, a0, a1
        ld      a1, 8(sp)
        sd      a0, 0(a1)
        ld      a0, 40(sp)
        ld      a1, 32(sp)
        sub     a0, a0, a1
        ld      a1, 24(sp)
        mul     a0, a0, a1
        ld      a1, 16(sp)
        rem     a0, a0, a1
        ld      a1, 0(sp)
        sd      a0, 0(a1)
        ld      ra, 56(sp)
        ld      s0, 48(sp)
        addi    sp, sp, 64
        ret

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
        beqz    a0, .LBB4_2
        j       .LBB4_1
.LBB4_1:
        ld      a0, 168(sp)
        sd      a0, 40(sp)
        j       .LBB4_3
.LBB4_2:
        li      a0, 2
        sd      a0, 40(sp)
        j       .LBB4_3
.LBB4_3:
        ld      a0, 40(sp)
        sd      a0, 128(sp)
        ld      a0, 144(sp)
        beqz    a0, .LBB4_5
        j       .LBB4_4
.LBB4_4:
        li      a0, 1
        sd      a0, 32(sp)
        j       .LBB4_6
.LBB4_5:
        ld      a0, 136(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 32(sp)
        j       .LBB4_6
.LBB4_6:
        ld      a0, 32(sp)
        sd      a0, 120(sp)
        ld      a0, 168(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 112(sp)
        li      a0, 0
        sd      a0, 104(sp)
        j       .LBB4_7
.LBB4_7:
        ld      a0, 104(sp)
        sd      a0, 24(sp)
        ld      a0, 168(sp)
        sd      a0, 184(sp)
        ld      a0, 184(sp)
        sd      a0, 200(sp)
        li      a0, 0
        sd      a0, 192(sp)
        j       .LBB4_8
.LBB4_8:
        ld      a0, 200(sp)
        li      a1, 2
        blt     a0, a1, .LBB4_10
        j       .LBB4_9
.LBB4_9:
        ld      a0, 200(sp)
        srai    a0, a0, 1
        sd      a0, 200(sp)
        ld      a0, 192(sp)
        addi    a0, a0, 1
        sd      a0, 192(sp)
        j       .LBB4_8
.LBB4_10:
        ld      a0, 24(sp)
        ld      a1, 192(sp)
        bge     a0, a1, .LBB4_27
        j       .LBB4_11
.LBB4_11:
        li      a0, 0
        sd      a0, 96(sp)
        j       .LBB4_12
.LBB4_12:
        ld      a0, 96(sp)
        ld      a1, 168(sp)
        ld      a2, 128(sp)
        div     a1, a1, a2
        bge     a0, a1, .LBB4_19
        j       .LBB4_13
.LBB4_13:
        li      a0, 0
        sd      a0, 88(sp)
        j       .LBB4_14
.LBB4_14:
        ld      a0, 88(sp)
        ld      a1, 128(sp)
        srli    a2, a1, 63
        add     a1, a1, a2
        srai    a1, a1, 1
        bge     a0, a1, .LBB4_17
        j       .LBB4_15
.LBB4_15:
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
        sd      a3, 248(sp)
        sd      a2, 240(sp)
        sd      a1, 232(sp)
        sd      a0, 224(sp)
        addi    a0, sp, 56
        sd      a0, 216(sp)
        addi    a0, sp, 48
        sd      a0, 208(sp)
        ld      a0, 248(sp)
        ld      a1, 232(sp)
        ld      a2, 240(sp)
        mul     a2, a1, a2
        ld      a1, 224(sp)
        rem     a2, a2, a1
        add     a0, a0, a2
        rem     a0, a0, a1
        ld      a1, 216(sp)
        sd      a0, 0(a1)
        ld      a0, 248(sp)
        ld      a1, 232(sp)
        ld      a2, 240(sp)
        mul     a2, a1, a2
        ld      a1, 224(sp)
        rem     a2, a2, a1
        sub     a0, a0, a2
        add     a0, a0, a1
        rem     a0, a0, a1
        ld      a1, 208(sp)
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
        j       .LBB4_16
.LBB4_16:
        ld      a0, 88(sp)
        addi    a0, a0, 1
        sd      a0, 88(sp)
        j       .LBB4_14
.LBB4_17:
        j       .LBB4_18
.LBB4_18:
        ld      a0, 96(sp)
        addi    a0, a0, 1
        sd      a0, 96(sp)
        j       .LBB4_12
.LBB4_19:
        ld      a0, 112(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 112(sp)
        ld      a0, 144(sp)
        beqz    a0, .LBB4_21
        j       .LBB4_20
.LBB4_20:
        ld      a0, 128(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 16(sp)
        j       .LBB4_22
.LBB4_21:
        ld      a0, 128(sp)
        slli    a0, a0, 1
        sd      a0, 16(sp)
        j       .LBB4_22
.LBB4_22:
        ld      a0, 16(sp)
        sd      a0, 128(sp)
        ld      a0, 144(sp)
        beqz    a0, .LBB4_24
        j       .LBB4_23
.LBB4_23:
        ld      a0, 120(sp)
        slli    a0, a0, 1
        sd      a0, 8(sp)
        j       .LBB4_25
.LBB4_24:
        ld      a0, 120(sp)
        srli    a1, a0, 63
        add     a0, a0, a1
        srai    a0, a0, 1
        sd      a0, 8(sp)
        j       .LBB4_25
.LBB4_25:
        ld      a0, 8(sp)
        sd      a0, 120(sp)
        j       .LBB4_26
.LBB4_26:
        ld      a0, 104(sp)
        addi    a0, a0, 1
        sd      a0, 104(sp)
        j       .LBB4_7
.LBB4_27:
        ld      ra, 264(sp)
        ld      s0, 256(sp)
        addi    sp, sp, 272
        ret