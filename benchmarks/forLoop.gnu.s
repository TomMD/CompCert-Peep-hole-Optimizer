	.file	"forLoop.c"
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC0:
	.string	"%d\n"
	.text
	.p2align 4,,15
.globl main
	.type	main, @function
main:
.LFB11:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	subq	$1040, %rsp
	.cfi_def_cfa_offset 1056
	movq	%rsp, %rdi
	.cfi_offset 3, -16
	call	gets
	leaq	1036(%rsp), %rdx
	movq	%rsp, %rsi
	movl	$.LC0, %edi
	xorl	%eax, %eax
	call	__isoc99_sscanf
	movl	1036(%rsp), %edx
	xorl	%esi, %esi
	xorl	%eax, %eax
	.p2align 4,,10
	.p2align 3
.L2:
	addl	%eax, %esi
	addl	%edx, %eax
	cmpl	$9999, %eax
	jle	.L2


	movl	$.LC0, %edi
	xorl	%eax, %eax
	call	printf
	xorl	%eax, %eax
	addq	$1040, %rsp
	popq	%rbx
	ret
	.cfi_endproc
.LFE11:
	.size	main, .-main
	.ident	"GCC: (Debian 4.4.5-13) 4.4.5"
	.section	.note.GNU-stack,"",@progbits
