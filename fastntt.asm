log2FloorAux:
        addi    sp, sp, -32
        sd      ra, 24(sp)
        sd      s0, 16(sp)
        addi    s0, sp, 32
        sw      a0, -20(s0)
        li      a0, 0
        sw      a0, -24(s0)
        j       .LBB0_1
.LBB0_1:
        lw      a0, -20(s0)
        li      a1, 2
        blt     a0, a1, .LBB0_3
        j       .LBB0_2
.LBB0_2:
        lw      a0, -20(s0)
        srli    a0, a0, 1
        sw      a0, -20(s0)
        lw      a0, -24(s0)
        addiw   a0, a0, 1
        sw      a0, -24(s0)
        j       .LBB0_1
.LBB0_3:
        lw      a0, -24(s0)
        ld      ra, 24(sp)
        ld      s0, 16(sp)
        addi    sp, sp, 32
        ret

log2Floor:
        addi    sp, sp, -32
        sd      ra, 24(sp)
        sd      s0, 16(sp)
        addi    s0, sp, 32
        sw      a0, -28(s0)
        lw      a0, -28(s0)
        sw      a0, -20(s0)
        li      a0, 0
        sw      a0, -24(s0)
        j       .LBB1_1
.LBB1_1:
        lw      a0, -20(s0)
        li      a1, 2
        blt     a0, a1, .LBB1_3
        j       .LBB1_2
.LBB1_2:
        lw      a0, -20(s0)
        srli    a0, a0, 1
        sw      a0, -20(s0)
        lw      a0, -24(s0)
        addiw   a0, a0, 1
        sw      a0, -24(s0)
        j       .LBB1_1
.LBB1_3:
        lw      a0, -24(s0)
        ld      ra, 24(sp)
        ld      s0, 16(sp)
        addi    sp, sp, 32
        ret

bflyCT:
        addi    sp, sp, -48
        sd      ra, 40(sp)
        sd      s0, 32(sp)
        addi    s0, sp, 48
        sw      a0, -20(s0)
        sw      a1, -24(s0)
        sw      a2, -28(s0)
        sw      a3, -32(s0)
        sd      a4, -40(s0)
        sd      a5, -48(s0)
        lw      a0, -20(s0)
        lw      a1, -28(s0)
        lw      a2, -24(s0)
        mulw    a2, a1, a2
        lw      a1, -32(s0)
        remw    a2, a2, a1
        addw    a0, a0, a2
        remw    a0, a0, a1
        ld      a1, -40(s0)
        sw      a0, 0(a1)
        lw      a0, -20(s0)
        lw      a1, -28(s0)
        lw      a2, -24(s0)
        mulw    a2, a1, a2
        lw      a1, -32(s0)
        remw    a2, a2, a1
        subw    a0, a0, a2
        addw    a0, a0, a1
        remw    a0, a0, a1
        ld      a1, -48(s0)
        sw      a0, 0(a1)
        ld      ra, 40(sp)
        ld      s0, 32(sp)
        addi    sp, sp, 48
        ret

bflyGS:
        addi    sp, sp, -48
        sd      ra, 40(sp)
        sd      s0, 32(sp)
        addi    s0, sp, 48
        sw      a0, -20(s0)
        sw      a1, -24(s0)
        sw      a2, -28(s0)
        sw      a3, -32(s0)
        sd      a4, -40(s0)
        sd      a5, -48(s0)
        lw      a0, -20(s0)
        lw      a1, -24(s0)
        addw    a0, a0, a1
        lw      a1, -32(s0)
        remw    a0, a0, a1
        ld      a1, -40(s0)
        sw      a0, 0(a1)
        lw      a0, -20(s0)
        lw      a1, -24(s0)
        subw    a0, a0, a1
        lw      a1, -28(s0)
        mulw    a0, a0, a1
        lw      a1, -32(s0)
        remw    a0, a0, a1
        ld      a1, -48(s0)
        sw      a0, 0(a1)
        ld      ra, 40(sp)
        ld      s0, 32(sp)
        addi    sp, sp, 48
        ret

fastNTT:
        addi    sp, sp, -192
        sd      ra, 184(sp)
        sd      s0, 176(sp)
        addi    s0, sp, 192
        sd      a0, -72(s0)
        sw      a1, -76(s0)
        sw      a2, -80(s0)
        sd      a3, -88(s0)
        sw      a4, -92(s0)
        sw      a5, -96(s0)
        lw      a0, -92(s0)
        beqz    a0, .LBB4_2
        j       .LBB4_1
.LBB4_1:
        lw      a0, -76(s0)
        sd      a0, -152(s0)
        j       .LBB4_3
.LBB4_2:
        li      a0, 2
        sd      a0, -152(s0)
        j       .LBB4_3
.LBB4_3:
        ld      a0, -152(s0)
        sw      a0, -100(s0)
        lw      a0, -92(s0)
        beqz    a0, .LBB4_5
        j       .LBB4_4
.LBB4_4:
        li      a0, 1
        sd      a0, -160(s0)
        j       .LBB4_6
.LBB4_5:
        lw      a0, -96(s0)
        srliw   a1, a0, 31
        addw    a0, a0, a1
        sraiw   a0, a0, 1
        sd      a0, -160(s0)
        j       .LBB4_6
.LBB4_6:
        ld      a0, -160(s0)
        sw      a0, -104(s0)
        lw      a0, -76(s0)
        srliw   a1, a0, 31
        addw    a0, a0, a1
        sraiw   a0, a0, 1
        sw      a0, -108(s0)
        li      a0, 0
        sw      a0, -112(s0)
        j       .LBB4_7
.LBB4_7:
        lw      a0, -112(s0)
        sd      a0, -168(s0)
        lw      a0, -76(s0)
        sw      a0, -60(s0)
        lw      a0, -60(s0)
        sw      a0, -52(s0)
        li      a0, 0
        sw      a0, -56(s0)
        j       .LBB4_8
.LBB4_8:
        lw      a0, -52(s0)
        li      a1, 2
        blt     a0, a1, .LBB4_10
        j       .LBB4_9
.LBB4_9:
        lw      a0, -52(s0)
        srli    a0, a0, 1
        sw      a0, -52(s0)
        lw      a0, -56(s0)
        addiw   a0, a0, 1
        sw      a0, -56(s0)
        j       .LBB4_8
.LBB4_10:
        ld      a0, -168(s0)
        lw      a1, -56(s0)
        sext.w  a0, a0
        bge     a0, a1, .LBB4_27
        j       .LBB4_11
.LBB4_11:
        li      a0, 0
        sw      a0, -116(s0)
        j       .LBB4_12
.LBB4_12:
        lw      a0, -116(s0)
        lw      a1, -76(s0)
        lw      a2, -100(s0)
        divw    a1, a1, a2
        bge     a0, a1, .LBB4_19
        j       .LBB4_13
.LBB4_13:
        li      a0, 0
        sw      a0, -120(s0)
        j       .LBB4_14
.LBB4_14:
        lw      a0, -120(s0)
        lw      a1, -100(s0)
        srliw   a2, a1, 31
        addw    a1, a1, a2
        sraiw   a1, a1, 1
        bge     a0, a1, .LBB4_17
        j       .LBB4_15
.LBB4_15:
        ld      a0, -72(s0)
        lw      a1, -116(s0)
        lw      a2, -100(s0)
        mulw    a1, a1, a2
        lw      a2, -120(s0)
        addw    a1, a1, a2
        slli    a1, a1, 2
        add     a0, a0, a1
        lw      a0, 0(a0)
        sw      a0, -124(s0)
        ld      a0, -72(s0)
        lw      a1, -116(s0)
        lw      a2, -100(s0)
        mulw    a1, a1, a2
        lw      a3, -120(s0)
        addw    a1, a1, a3
        srliw   a3, a2, 31
        addw    a2, a2, a3
        sraiw   a2, a2, 1
        addw    a1, a1, a2
        slli    a1, a1, 2
        add     a0, a0, a1
        lw      a0, 0(a0)
        sw      a0, -128(s0)
        ld      a0, -88(s0)
        lw      a1, -120(s0)
        slli    a1, a1, 1
        addi    a1, a1, 1
        lw      a2, -108(s0)
        mulw    a1, a1, a2
        slli    a1, a1, 2
        add     a0, a0, a1
        lw      a0, 0(a0)
        sw      a0, -132(s0)
        lw      a3, -124(s0)
        lw      a2, -128(s0)
        lw      a1, -132(s0)
        lw      a0, -80(s0)
        sw      a3, -20(s0)
        sw      a2, -24(s0)
        sw      a1, -28(s0)
        sw      a0, -32(s0)
        addi    a0, s0, -136
        sd      a0, -40(s0)
        addi    a0, s0, -140
        sd      a0, -48(s0)
        lw      a0, -20(s0)
        lw      a1, -28(s0)
        lw      a2, -24(s0)
        mulw    a2, a1, a2
        lw      a1, -32(s0)
        remw    a2, a2, a1
        addw    a0, a0, a2
        remw    a0, a0, a1
        ld      a1, -40(s0)
        sw      a0, 0(a1)
        lw      a0, -20(s0)
        lw      a1, -28(s0)
        lw      a2, -24(s0)
        mulw    a2, a1, a2
        lw      a1, -32(s0)
        remw    a2, a2, a1
        subw    a0, a0, a2
        addw    a0, a0, a1
        remw    a0, a0, a1
        ld      a1, -48(s0)
        sw      a0, 0(a1)
        lw      a0, -136(s0)
        ld      a1, -72(s0)
        lw      a2, -116(s0)
        lw      a3, -100(s0)
        mulw    a2, a2, a3
        lw      a3, -120(s0)
        addw    a2, a2, a3
        slli    a2, a2, 2
        add     a1, a1, a2
        sw      a0, 0(a1)
        lw      a0, -140(s0)
        ld      a1, -72(s0)
        lw      a2, -116(s0)
        lw      a3, -100(s0)
        mulw    a2, a2, a3
        lw      a4, -120(s0)
        addw    a2, a2, a4
        srliw   a4, a3, 31
        addw    a3, a3, a4
        sraiw   a3, a3, 1
        addw    a2, a2, a3
        slli    a2, a2, 2
        add     a1, a1, a2
        sw      a0, 0(a1)
        j       .LBB4_16
.LBB4_16:
        lw      a0, -120(s0)
        addiw   a0, a0, 1
        sw      a0, -120(s0)
        j       .LBB4_14
.LBB4_17:
        j       .LBB4_18
.LBB4_18:
        lw      a0, -116(s0)
        addiw   a0, a0, 1
        sw      a0, -116(s0)
        j       .LBB4_12
.LBB4_19:
        lw      a0, -108(s0)
        srliw   a1, a0, 31
        addw    a0, a0, a1
        sraiw   a0, a0, 1
        sw      a0, -108(s0)
        lw      a0, -92(s0)
        beqz    a0, .LBB4_21
        j       .LBB4_20
.LBB4_20:
        lw      a0, -100(s0)
        srliw   a1, a0, 31
        addw    a0, a0, a1
        sraiw   a0, a0, 1
        sd      a0, -176(s0)
        j       .LBB4_22
.LBB4_21:
        lw      a0, -100(s0)
        slliw   a0, a0, 1
        sd      a0, -176(s0)
        j       .LBB4_22
.LBB4_22:
        ld      a0, -176(s0)
        sw      a0, -100(s0)
        lw      a0, -92(s0)
        beqz    a0, .LBB4_24
        j       .LBB4_23
.LBB4_23:
        lw      a0, -104(s0)
        slliw   a0, a0, 1
        sd      a0, -184(s0)
        j       .LBB4_25
.LBB4_24:
        lw      a0, -104(s0)
        srliw   a1, a0, 31
        addw    a0, a0, a1
        sraiw   a0, a0, 1
        sd      a0, -184(s0)
        j       .LBB4_25
.LBB4_25:
        ld      a0, -184(s0)
        sw      a0, -104(s0)
        j       .LBB4_26
.LBB4_26:
        lw      a0, -112(s0)
        addiw   a0, a0, 1
        sw      a0, -112(s0)
        j       .LBB4_7
.LBB4_27:
        ld      ra, 184(sp)
        ld      s0, 176(sp)
        addi    sp, sp, 192
        ret