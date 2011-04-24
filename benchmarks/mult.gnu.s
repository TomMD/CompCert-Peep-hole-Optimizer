	.file	"mult.c"
	.text
.globl mult4
	.type	mult4, @function
mult4:
	pushl	%ebp
	movl	%esp, %ebp
	movl	8(%ebp), %eax
	sall	$2, %eax
	popl	%ebp
	ret
	.size	mult4, .-mult4
.globl mult2
	.type	mult2, @function
mult2:
	pushl	%ebp
	movl	%esp, %ebp
	movl	8(%ebp), %eax
	addl	%eax, %eax
	popl	%ebp
	ret
	.size	mult2, .-mult2
.globl mult1
	.type	mult1, @function
mult1:
	pushl	%ebp
	movl	%esp, %ebp
	movl	8(%ebp), %eax
	popl	%ebp
	ret
	.size	mult1, .-mult1
	.ident	"GCC: (Debian 4.4.6-2) 4.4.6"
	.section	.note.GNU-stack,"",@progbits
