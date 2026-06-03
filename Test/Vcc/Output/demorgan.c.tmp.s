	.text
	.file	"LLVMDialectModule"
	.globl	d1                              # -- Begin function d1
	.p2align	4, 0x90
	.type	d1,@function
d1:                                     # @d1
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	movl	%edi, %eax
	xorl	$-1, %eax
	xorl	$-1, %esi
	andl	%esi, %eax
	xorl	$-1, %eax
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end0:
	.size	d1, .Lfunc_end0-d1
	.cfi_endproc
                                        # -- End function
	.globl	d2                              # -- Begin function d2
	.p2align	4, 0x90
	.type	d2,@function
d2:                                     # @d2
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	movw	%si, %cx
	movw	%di, %ax
	movzwl	%ax, %eax
	xorl	$-1, %eax
	movzwl	%cx, %ecx
	xorl	$-1, %ecx
	orl	%ecx, %eax
	xorl	$-1, %eax
                                        # kill: def $ax killed $ax killed $eax
	movzwl	%ax, %eax
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end1:
	.size	d2, .Lfunc_end1-d2
	.cfi_endproc
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
