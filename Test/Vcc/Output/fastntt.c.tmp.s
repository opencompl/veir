	.text
	.file	"LLVMDialectModule"
	.globl	fastNTT                         # -- Begin function fastNTT
	.p2align	4, 0x90
	.type	fastNTT,@function
fastNTT:                                # @fastNTT
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	subq	$152, %rsp
	movq	%rdi, -48(%rbp)                 # 8-byte Spill
	movq	%rsi, -40(%rbp)                 # 8-byte Spill
	movq	%rdx, -32(%rbp)                 # 8-byte Spill
	movq	%rcx, -24(%rbp)                 # 8-byte Spill
	movq	%r8, -16(%rbp)                  # 8-byte Spill
	movq	%r9, -8(%rbp)                   # 8-byte Spill
	cmpq	$0, %r8
	je	.LBB0_2
# %bb.1:
	movq	-40(%rbp), %rax                 # 8-byte Reload
	movq	%rax, -56(%rbp)                 # 8-byte Spill
	jmp	.LBB0_3
.LBB0_2:
	movl	$2, %eax
	movq	%rax, -56(%rbp)                 # 8-byte Spill
	jmp	.LBB0_3
.LBB0_3:
	movq	-16(%rbp), %rax                 # 8-byte Reload
	movq	-56(%rbp), %rcx                 # 8-byte Reload
	movq	%rcx, -64(%rbp)                 # 8-byte Spill
	cmpq	$0, %rax
	je	.LBB0_5
# %bb.4:
	movl	$1, %eax
	movq	%rax, -72(%rbp)                 # 8-byte Spill
	jmp	.LBB0_6
.LBB0_5:
	movq	-8(%rbp), %rax                  # 8-byte Reload
	movl	$2, %ecx
	cqto
	idivq	%rcx
	movq	%rax, -72(%rbp)                 # 8-byte Spill
.LBB0_6:
	movq	-40(%rbp), %rax                 # 8-byte Reload
	movq	-72(%rbp), %rsi                 # 8-byte Reload
	movl	$2, %ecx
	cqto
	idivq	%rcx
	movq	%rax, %rdx
	movq	-64(%rbp), %rax                 # 8-byte Reload
	xorl	%ecx, %ecx
                                        # kill: def $rcx killed $ecx
	movq	%rsi, -104(%rbp)                # 8-byte Spill
	movq	%rdx, -96(%rbp)                 # 8-byte Spill
	movq	%rcx, -88(%rbp)                 # 8-byte Spill
	movq	%rax, -80(%rbp)                 # 8-byte Spill
.LBB0_7:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB0_8 Depth 2
                                        #     Child Loop BB0_12 Depth 2
                                        #       Child Loop BB0_14 Depth 3
	movq	-40(%rbp), %rax                 # 8-byte Reload
	movq	-104(%rbp), %rcx                # 8-byte Reload
	movq	-96(%rbp), %rdx                 # 8-byte Reload
	movq	-88(%rbp), %rsi                 # 8-byte Reload
	movq	-80(%rbp), %rdi                 # 8-byte Reload
	movq	%rdi, -152(%rbp)                # 8-byte Spill
	movq	%rsi, -144(%rbp)                # 8-byte Spill
	movq	%rdx, -136(%rbp)                # 8-byte Spill
	movq	%rcx, -128(%rbp)                # 8-byte Spill
	xorl	%ecx, %ecx
                                        # kill: def $rcx killed $ecx
	movq	%rcx, -120(%rbp)                # 8-byte Spill
	movq	%rax, -112(%rbp)                # 8-byte Spill
.LBB0_8:                                #   Parent Loop BB0_7 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	movq	-120(%rbp), %rcx                # 8-byte Reload
	movq	-112(%rbp), %rax                # 8-byte Reload
	movq	%rax, -168(%rbp)                # 8-byte Spill
	movq	%rcx, -160(%rbp)                # 8-byte Spill
	cmpq	$1, %rax
	jle	.LBB0_10
# %bb.9:                                #   in Loop: Header=BB0_8 Depth=2
	movq	-160(%rbp), %rcx                # 8-byte Reload
	movq	-168(%rbp), %rax                # 8-byte Reload
	sarq	%rax
	addq	$1, %rcx
	movq	%rcx, -120(%rbp)                # 8-byte Spill
	movq	%rax, -112(%rbp)                # 8-byte Spill
	jmp	.LBB0_8
.LBB0_10:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-144(%rbp), %rax                # 8-byte Reload
	movq	-160(%rbp), %rcx                # 8-byte Reload
	cmpq	%rcx, %rax
	jge	.LBB0_27
# %bb.11:                               #   in Loop: Header=BB0_7 Depth=1
	xorl	%eax, %eax
                                        # kill: def $rax killed $eax
	movq	%rax, -176(%rbp)                # 8-byte Spill
	jmp	.LBB0_12
.LBB0_12:                               #   Parent Loop BB0_7 Depth=1
                                        # =>  This Loop Header: Depth=2
                                        #       Child Loop BB0_14 Depth 3
	movq	-152(%rbp), %rcx                # 8-byte Reload
	movq	-40(%rbp), %rax                 # 8-byte Reload
	movq	-176(%rbp), %rdx                # 8-byte Reload
	movq	%rdx, -184(%rbp)                # 8-byte Spill
	cqto
	idivq	%rcx
	movq	%rax, %rcx
	movq	-184(%rbp), %rax                # 8-byte Reload
	cmpq	%rcx, %rax
	jge	.LBB0_19
# %bb.13:                               #   in Loop: Header=BB0_12 Depth=2
	xorl	%eax, %eax
                                        # kill: def $rax killed $eax
	movq	%rax, -192(%rbp)                # 8-byte Spill
	jmp	.LBB0_14
.LBB0_14:                               #   Parent Loop BB0_7 Depth=1
                                        #     Parent Loop BB0_12 Depth=2
                                        # =>    This Inner Loop Header: Depth=3
	movq	-152(%rbp), %rax                # 8-byte Reload
	movq	-192(%rbp), %rcx                # 8-byte Reload
	movq	%rcx, -200(%rbp)                # 8-byte Spill
	movl	$2, %ecx
	cqto
	idivq	%rcx
	movq	%rax, %rcx
	movq	-200(%rbp), %rax                # 8-byte Reload
	cmpq	%rcx, %rax
	jge	.LBB0_17
# %bb.15:                               #   in Loop: Header=BB0_14 Depth=3
	movq	-48(%rbp), %rsi                 # 8-byte Reload
	movq	-152(%rbp), %rax                # 8-byte Reload
	movq	-200(%rbp), %r8                 # 8-byte Reload
	movq	-184(%rbp), %rcx                # 8-byte Reload
	movq	-32(%rbp), %rdi                 # 8-byte Reload
	movq	-136(%rbp), %r9                 # 8-byte Reload
	movq	%rcx, %rdx
	imulq	%rax, %rdx
	addq	%r8, %rdx
	movq	(%rsi,%rdx,8), %rdx
	movq	%rdx, -216(%rbp)                # 8-byte Spill
	movq	%rcx, %rdx
	imulq	%rax, %rdx
	addq	%r8, %rdx
	movq	%rdx, -240(%rbp)                # 8-byte Spill
	movl	$2, %r10d
	cqto
	idivq	%r10
	movq	-240(%rbp), %rdx                # 8-byte Reload
	movq	%rax, %r10
	movq	-24(%rbp), %rax                 # 8-byte Reload
	addq	%r10, %rdx
	movq	(%rsi,%rdx,8), %rdx
	movq	%rdx, -224(%rbp)                # 8-byte Spill
	shlq	%r8
	addq	$1, %r8
	imulq	%r9, %r8
	movq	(%rax,%r8,8), %rax
	movq	%rax, -232(%rbp)                # 8-byte Spill
	imulq	%rdx, %rax
	cqto
	idivq	%rdi
	movq	-216(%rbp), %rax                # 8-byte Reload
	addq	%rdx, %rax
	cqto
	idivq	%rdi
	movq	-232(%rbp), %rax                # 8-byte Reload
	movq	%rdx, %r8
	movq	-224(%rbp), %rdx                # 8-byte Reload
	imulq	%rdx, %rax
	cqto
	idivq	%rdi
	movq	-216(%rbp), %rax                # 8-byte Reload
	subq	%rdx, %rax
	addq	%rdi, %rax
	cqto
	idivq	%rdi
	movq	-152(%rbp), %rax                # 8-byte Reload
	movq	%rdx, %rdi
	movq	-200(%rbp), %rdx                # 8-byte Reload
	movq	%rdi, -208(%rbp)                # 8-byte Spill
	movq	%rcx, %rdi
	imulq	%rax, %rdi
	addq	%rdx, %rdi
	movq	%r8, (%rsi,%rdi,8)
	imulq	%rax, %rcx
	addq	%rdx, %rcx
	movl	$2, %esi
	cqto
	idivq	%rsi
	movq	-208(%rbp), %rdx                # 8-byte Reload
	movq	%rax, %rsi
	movq	-48(%rbp), %rax                 # 8-byte Reload
	addq	%rsi, %rcx
	movq	%rdx, (%rax,%rcx,8)
# %bb.16:                               #   in Loop: Header=BB0_14 Depth=3
	movq	-200(%rbp), %rax                # 8-byte Reload
	addq	$1, %rax
	movq	%rax, -192(%rbp)                # 8-byte Spill
	jmp	.LBB0_14
.LBB0_17:                               #   in Loop: Header=BB0_12 Depth=2
	jmp	.LBB0_18
.LBB0_18:                               #   in Loop: Header=BB0_12 Depth=2
	movq	-184(%rbp), %rax                # 8-byte Reload
	addq	$1, %rax
	movq	%rax, -176(%rbp)                # 8-byte Spill
	jmp	.LBB0_12
.LBB0_19:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-136(%rbp), %rax                # 8-byte Reload
	movl	$2, %ecx
	cqto
	idivq	%rcx
	movq	%rax, %rcx
	movq	-16(%rbp), %rax                 # 8-byte Reload
	movq	%rcx, -248(%rbp)                # 8-byte Spill
	cmpq	$0, %rax
	je	.LBB0_21
# %bb.20:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-152(%rbp), %rax                # 8-byte Reload
	movl	$2, %ecx
	cqto
	idivq	%rcx
	movq	%rax, -256(%rbp)                # 8-byte Spill
	jmp	.LBB0_22
.LBB0_21:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-152(%rbp), %rax                # 8-byte Reload
	shlq	%rax
	movq	%rax, -256(%rbp)                # 8-byte Spill
.LBB0_22:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-16(%rbp), %rax                 # 8-byte Reload
	movq	-256(%rbp), %rcx                # 8-byte Reload
	movq	%rcx, -264(%rbp)                # 8-byte Spill
	cmpq	$0, %rax
	je	.LBB0_24
# %bb.23:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-128(%rbp), %rax                # 8-byte Reload
	shlq	%rax
	movq	%rax, -272(%rbp)                # 8-byte Spill
	jmp	.LBB0_25
.LBB0_24:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-128(%rbp), %rax                # 8-byte Reload
	movl	$2, %ecx
	cqto
	idivq	%rcx
	movq	%rax, -272(%rbp)                # 8-byte Spill
.LBB0_25:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-272(%rbp), %rax                # 8-byte Reload
	movq	%rax, -280(%rbp)                # 8-byte Spill
# %bb.26:                               #   in Loop: Header=BB0_7 Depth=1
	movq	-264(%rbp), %rax                # 8-byte Reload
	movq	-248(%rbp), %rdx                # 8-byte Reload
	movq	-280(%rbp), %rsi                # 8-byte Reload
	movq	-144(%rbp), %rcx                # 8-byte Reload
	addq	$1, %rcx
	movq	%rsi, -104(%rbp)                # 8-byte Spill
	movq	%rdx, -96(%rbp)                 # 8-byte Spill
	movq	%rcx, -88(%rbp)                 # 8-byte Spill
	movq	%rax, -80(%rbp)                 # 8-byte Spill
	jmp	.LBB0_7
.LBB0_27:
	addq	$152, %rsp
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end0:
	.size	fastNTT, .Lfunc_end0-fastNTT
	.cfi_endproc
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
