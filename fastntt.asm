	.att_syntax
	.file	"fastntt.cpp"
	.text
	.globl	_Z6bflyCTiiiiRiS_               # -- Begin function _Z6bflyCTiiiiRiS_
	.p2align	4
	.type	_Z6bflyCTiiiiRiS_,@function
_Z6bflyCTiiiiRiS_:                      # @_Z6bflyCTiiiiRiS_
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	movl	%edi, -16(%rbp)
	movl	%esi, -12(%rbp)
	movl	%edx, -8(%rbp)
	movl	%ecx, -4(%rbp)
	movq	%r8, -32(%rbp)
	movq	%r9, -24(%rbp)
	movl	-16(%rbp), %ecx
	movl	-8(%rbp), %eax
	imull	-12(%rbp), %eax
	cltd
	idivl	-4(%rbp)
	addl	%edx, %ecx
	movl	%ecx, %eax
	cltd
	idivl	-4(%rbp)
	movq	-32(%rbp), %rax
	movl	%edx, (%rax)
	movl	-16(%rbp), %ecx
	movl	-8(%rbp), %eax
	imull	-12(%rbp), %eax
	cltd
	idivl	-4(%rbp)
	subl	%edx, %ecx
	addl	-4(%rbp), %ecx
	movl	%ecx, %eax
	cltd
	idivl	-4(%rbp)
	movq	-24(%rbp), %rax
	movl	%edx, (%rax)
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end0:
	.size	_Z6bflyCTiiiiRiS_, .Lfunc_end0-_Z6bflyCTiiiiRiS_
	.cfi_endproc
                                        # -- End function
	.globl	_Z6bflyGSiiiiRiS_               # -- Begin function _Z6bflyGSiiiiRiS_
	.p2align	4
	.type	_Z6bflyGSiiiiRiS_,@function
_Z6bflyGSiiiiRiS_:                      # @_Z6bflyGSiiiiRiS_
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	movl	%edi, -12(%rbp)
	movl	%esi, -8(%rbp)
	movl	%edx, -16(%rbp)
	movl	%ecx, -4(%rbp)
	movq	%r8, -32(%rbp)
	movq	%r9, -24(%rbp)
	movl	-12(%rbp), %eax
	addl	-8(%rbp), %eax
	cltd
	idivl	-4(%rbp)
	movq	-32(%rbp), %rax
	movl	%edx, (%rax)
	movl	-12(%rbp), %eax
	subl	-8(%rbp), %eax
	imull	-16(%rbp), %eax
	cltd
	idivl	-4(%rbp)
	movq	-24(%rbp), %rax
	movl	%edx, (%rax)
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end1:
	.size	_Z6bflyGSiiiiRiS_, .Lfunc_end1-_Z6bflyGSiiiiRiS_
	.cfi_endproc
                                        # -- End function
	.globl	_Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b # -- Begin function _Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b
	.p2align	4
	.type	_Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b,@function
_Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b:   # @_Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	pushq	%rbx
	subq	$72, %rsp
	.cfi_offset %rbx, -24
	movq	%rdi, -48(%rbp)
	movl	%esi, -28(%rbp)
	movl	%edx, -72(%rbp)
	movq	%rcx, -80(%rbp)
	andb	$1, %r8b
	movb	%r8b, -9(%rbp)
	testb	$1, -9(%rbp)
	je	.LBB2_2
# %bb.1:
	movl	-28(%rbp), %eax
	jmp	.LBB2_3
.LBB2_2:
	movl	$2, %eax
	jmp	.LBB2_3
.LBB2_3:
	movl	%eax, -16(%rbp)
	testb	$1, -9(%rbp)
	je	.LBB2_5
# %bb.4:
	movl	$1, %eax
	jmp	.LBB2_6
.LBB2_5:
	movl	-28(%rbp), %eax
	movl	$2, %ecx
	cltd
	idivl	%ecx
.LBB2_6:
	movl	%eax, -40(%rbp)
	movl	-28(%rbp), %eax
	movl	$2, %ecx
	cltd
	idivl	%ecx
	movl	%eax, -36(%rbp)
	movl	$0, -32(%rbp)
.LBB2_7:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB2_9 Depth 2
                                        #       Child Loop BB2_11 Depth 3
	movl	-32(%rbp), %eax
	movl	-28(%rbp), %ecx
	rep		bsfl	%ecx, %ecx
	cmpl	%ecx, %eax
	jge	.LBB2_24
# %bb.8:                                #   in Loop: Header=BB2_7 Depth=1
	movl	$0, -24(%rbp)
.LBB2_9:                                #   Parent Loop BB2_7 Depth=1
                                        # =>  This Loop Header: Depth=2
                                        #       Child Loop BB2_11 Depth 3
	movl	-24(%rbp), %ecx
	movl	-28(%rbp), %eax
	cltd
	idivl	-16(%rbp)
	cmpl	%eax, %ecx
	jge	.LBB2_16
# %bb.10:                               #   in Loop: Header=BB2_9 Depth=2
	movl	$0, -20(%rbp)
.LBB2_11:                               #   Parent Loop BB2_7 Depth=1
                                        #     Parent Loop BB2_9 Depth=2
                                        # =>    This Inner Loop Header: Depth=3
	movl	-20(%rbp), %ecx
	movl	-16(%rbp), %eax
	movl	$2, %esi
	cltd
	idivl	%esi
	cmpl	%eax, %ecx
	jge	.LBB2_14
# %bb.12:                               #   in Loop: Header=BB2_11 Depth=3
	movq	-48(%rbp), %rdi
	movl	-24(%rbp), %eax
	imull	-16(%rbp), %eax
	addl	-20(%rbp), %eax
	movslq	%eax, %rsi
	callq	_ZNSt6vectorIiSaIiEEixEm
	movl	(%rax), %eax
	movl	%eax, -68(%rbp)
	movq	-48(%rbp), %rdi
	movl	-24(%rbp), %ecx
	imull	-16(%rbp), %ecx
	addl	-20(%rbp), %ecx
	movl	-16(%rbp), %eax
	movl	$2, %esi
	cltd
	idivl	%esi
	addl	%eax, %ecx
	movslq	%ecx, %rsi
	callq	_ZNSt6vectorIiSaIiEEixEm
	movl	(%rax), %eax
	movl	%eax, -64(%rbp)
	movq	-80(%rbp), %rdi
	movl	-20(%rbp), %eax
	shll	%eax
	addl	$1, %eax
	imull	-36(%rbp), %eax
	movslq	%eax, %rsi
	callq	_ZNKSt6vectorIiSaIiEEixEm
	movl	(%rax), %eax
	movl	%eax, -60(%rbp)
	movl	-68(%rbp), %edi
	movl	-64(%rbp), %esi
	movl	-60(%rbp), %edx
	movl	-72(%rbp), %ecx
	leaq	-56(%rbp), %r8
	leaq	-52(%rbp), %r9
	callq	_Z6bflyCTiiiiRiS_
	movl	-56(%rbp), %ebx
	movq	-48(%rbp), %rdi
	movl	-24(%rbp), %eax
	imull	-16(%rbp), %eax
	addl	-20(%rbp), %eax
	movslq	%eax, %rsi
	callq	_ZNSt6vectorIiSaIiEEixEm
	movl	%ebx, (%rax)
	movl	-52(%rbp), %ebx
	movq	-48(%rbp), %rdi
	movl	-24(%rbp), %ecx
	imull	-16(%rbp), %ecx
	addl	-20(%rbp), %ecx
	movl	-16(%rbp), %eax
	movl	$2, %esi
	cltd
	idivl	%esi
	addl	%eax, %ecx
	movslq	%ecx, %rsi
	callq	_ZNSt6vectorIiSaIiEEixEm
	movl	%ebx, (%rax)
# %bb.13:                               #   in Loop: Header=BB2_11 Depth=3
	movl	-20(%rbp), %eax
	addl	$1, %eax
	movl	%eax, -20(%rbp)
	jmp	.LBB2_11
.LBB2_14:                               #   in Loop: Header=BB2_9 Depth=2
	jmp	.LBB2_15
.LBB2_15:                               #   in Loop: Header=BB2_9 Depth=2
	movl	-24(%rbp), %eax
	addl	$1, %eax
	movl	%eax, -24(%rbp)
	jmp	.LBB2_9
.LBB2_16:                               #   in Loop: Header=BB2_7 Depth=1
	movl	-36(%rbp), %eax
	movl	$2, %ecx
	cltd
	idivl	%ecx
	movl	%eax, -36(%rbp)
	testb	$1, -9(%rbp)
	je	.LBB2_18
# %bb.17:                               #   in Loop: Header=BB2_7 Depth=1
	movl	-16(%rbp), %eax
	movl	$2, %ecx
	cltd
	idivl	%ecx
	jmp	.LBB2_19
.LBB2_18:                               #   in Loop: Header=BB2_7 Depth=1
	movl	-16(%rbp), %eax
	shll	%eax
.LBB2_19:                               #   in Loop: Header=BB2_7 Depth=1
	movl	%eax, -16(%rbp)
	testb	$1, -9(%rbp)
	je	.LBB2_21
# %bb.20:                               #   in Loop: Header=BB2_7 Depth=1
	movl	-40(%rbp), %eax
	shll	%eax
	jmp	.LBB2_22
.LBB2_21:                               #   in Loop: Header=BB2_7 Depth=1
	movl	-40(%rbp), %eax
	movl	$2, %ecx
	cltd
	idivl	%ecx
.LBB2_22:                               #   in Loop: Header=BB2_7 Depth=1
	movl	%eax, -40(%rbp)
# %bb.23:                               #   in Loop: Header=BB2_7 Depth=1
	movl	-32(%rbp), %eax
	addl	$1, %eax
	movl	%eax, -32(%rbp)
	jmp	.LBB2_7
.LBB2_24:
	addq	$72, %rsp
	popq	%rbx
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end2:
	.size	_Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b, .Lfunc_end2-_Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b
	.cfi_endproc
                                        # -- End function
	.section	.text._ZNSt6vectorIiSaIiEEixEm,"axG",@progbits,_ZNSt6vectorIiSaIiEEixEm,comdat
	.weak	_ZNSt6vectorIiSaIiEEixEm        # -- Begin function _ZNSt6vectorIiSaIiEEixEm
	.p2align	4
	.type	_ZNSt6vectorIiSaIiEEixEm,@function
_ZNSt6vectorIiSaIiEEixEm:               # @_ZNSt6vectorIiSaIiEEixEm
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	movq	%rdi, -16(%rbp)
	movq	%rsi, -8(%rbp)
	movq	-16(%rbp), %rax
	movq	(%rax), %rax
	movq	-8(%rbp), %rcx
	shlq	$2, %rcx
	addq	%rcx, %rax
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end3:
	.size	_ZNSt6vectorIiSaIiEEixEm, .Lfunc_end3-_ZNSt6vectorIiSaIiEEixEm
	.cfi_endproc
                                        # -- End function
	.section	.text._ZNKSt6vectorIiSaIiEEixEm,"axG",@progbits,_ZNKSt6vectorIiSaIiEEixEm,comdat
	.weak	_ZNKSt6vectorIiSaIiEEixEm       # -- Begin function _ZNKSt6vectorIiSaIiEEixEm
	.p2align	4
	.type	_ZNKSt6vectorIiSaIiEEixEm,@function
_ZNKSt6vectorIiSaIiEEixEm:              # @_ZNKSt6vectorIiSaIiEEixEm
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	movq	%rdi, -16(%rbp)
	movq	%rsi, -8(%rbp)
	movq	-16(%rbp), %rax
	movq	(%rax), %rax
	movq	-8(%rbp), %rcx
	shlq	$2, %rcx
	addq	%rcx, %rax
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end4:
	.size	_ZNKSt6vectorIiSaIiEEixEm, .Lfunc_end4-_ZNKSt6vectorIiSaIiEEixEm
	.cfi_endproc
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
