	.file	"forLoop.c"
	.section	.rodata
.LC0:
	.string	"%d\n"
	.text
.globl main
	.type	main, @function
main:
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-16, %esp
	subl	$1056, %esp
	movl	$0, 1052(%esp)
	leal	20(%esp), %eax
	movl	%eax, (%esp)
	call	gets
	leal	20(%esp), %edx
	movl	$.LC0, %eax
	leal	1044(%esp), %ecx
	movl	%ecx, 8(%esp)
	movl	%edx, 4(%esp)
	movl	%eax, (%esp)
	call	__isoc99_sscanf
	movl	$0, 1048(%esp)
	jmp	.L2
.L3:
	movl	1048(%esp), %eax
	addl	%eax, 1052(%esp)
	movl	1044(%esp), %eax
	addl	%eax, 1048(%esp)
.L2:
	cmpl	$9999, 1048(%esp)
	jle	.L3
	movl	$.LC0, %eax
	movl	1052(%esp), %edx
	movl	%edx, 4(%esp)
	movl	%eax, (%esp)
	call	printf
	movl	$0, %eax
	leave
	ret
	.size	main, .-main
	.ident	"GCC: (Debian 4.4.6-2) 4.4.6"
	.section	.note.GNU-stack,"",@progbits
