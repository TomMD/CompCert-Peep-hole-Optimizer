	.section	.rodata
	.align	4
__stringlit_1:
	.ascii	"%d\012\000"
	.type	__stringlit_1, @object
	.size	__stringlit_1, . - __stringlit_1
	.text
	.align	16
	.globl main
main:
	subl	$1076, %esp
	leal	1080(%esp), %edx
	movl	%edx, 12(%esp)
	movl	%ebx, 24(%esp)
	movl	%esi, 28(%esp)
	movl	%edi, 32(%esp)
	xorl	%ebx, %ebx
	leal	48(%esp), %eax
	movl	%eax, 0(%esp)
	call	gets
	leal	__stringlit_1, %edi
	leal	48(%esp), %eax
	leal	40(%esp), %esi
	movl	%edi, 0(%esp)
	movl	%eax, 4(%esp)
	movl	%esi, 8(%esp)
	call	__isoc99_sscanf
	xorl	%esi, %esi
.L100:
	cmpl	$10000, %esi
	jge	.L101
	leal	0(%ebx,%esi,1), %ebx
	movl	40(%esp), %eax
	leal	0(%esi,%eax,1), %esi
	jmp	.L100
.L101:
	leal	__stringlit_1, %eax
	movl	%eax, 0(%esp)
	movl	%ebx, 4(%esp)
	call	printf
	xorl	%eax, %eax
	movl	24(%esp), %ebx
	movl	28(%esp), %esi
	movl	32(%esp), %edi
	addl	$1076, %esp
	ret
	.type	main, @function
	.size	main, . - main
