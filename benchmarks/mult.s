	.text
	.align	16
	.globl mult4
mult4:
	subl	$12, %esp
	leal	16(%esp), %edx
	movl	%edx, 0(%esp)
	movl	0(%esp), %edx
	movl	0(%edx), %eax
	leal	0(,%eax,4), %eax
	addl	$12, %esp
	ret
	.type	mult4, @function
	.size	mult4, . - mult4
	.text
	.align	16
	.globl mult2
mult2:
	subl	$12, %esp
	leal	16(%esp), %edx
	movl	%edx, 0(%esp)
	movl	0(%esp), %edx
	movl	0(%edx), %eax
	leal	0(,%eax,2), %eax
	addl	$12, %esp
	ret
	.type	mult2, @function
	.size	mult2, . - mult2
	.text
	.align	16
	.globl mult1
mult1:
	subl	$12, %esp
	leal	16(%esp), %edx
	movl	%edx, 0(%esp)
	movl	0(%esp), %edx
	movl	0(%edx), %eax
	addl	$12, %esp
	ret
	.type	mult1, @function
	.size	mult1, . - mult1
	.text
	.align	16
	.globl main
main:
	subl	$20, %esp
	leal	24(%esp), %edx
	movl	%edx, 4(%esp)
	movl	$13, %eax
	movl	%eax, 0(%esp)
	call	mult4
	movl	$13, %eax
	movl	%eax, 0(%esp)
	call	mult2
	movl	$13, %eax
	movl	%eax, 0(%esp)
	call	mult1
	xorl	%eax, %eax
	addl	$20, %esp
	ret
	.type	main, @function
	.size	main, . - main
