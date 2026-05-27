	.build_version macos, 26, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_d1                             ; -- Begin function d1
	.p2align	2
_d1:                                    ; @d1
	.cfi_startproc
; %bb.0:
	mvn	w8, w1
	bic	w8, w8, w0
	mvn	w0, w8
	ret
	.cfi_endproc
                                        ; -- End function
	.globl	_d2                             ; -- Begin function d2
	.p2align	2
_d2:                                    ; @d2
	.cfi_startproc
; %bb.0:
	mvn	w8, w1
	orn	w9, w8, w0
	mov	w8, #65535                      ; =0xffff
	bic	w0, w8, w9
	ret
	.cfi_endproc
                                        ; -- End function
.subsections_via_symbols
