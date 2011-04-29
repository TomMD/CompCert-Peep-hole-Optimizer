	.text
	.align 2
	.global	mult4
	.type	mult4, %function
mult4:
	mov	r12, sp
	sub	sp, sp, #8
	str	r12, [sp, #4]
	str	lr, [sp, #0]
	mov	r0, r0, lsl #2
	ldr	lr, [sp, #0]
	ldr	sp, [sp, #4]
	mov	pc, lr
	.text
	.align 2
	.global	mult2
	.type	mult2, %function
mult2:
	mov	r12, sp
	sub	sp, sp, #8
	str	r12, [sp, #4]
	str	lr, [sp, #0]
	mov	r0, r0, lsl #1
	ldr	lr, [sp, #0]
	ldr	sp, [sp, #4]
	mov	pc, lr
	.text
	.align 2
	.global	mult1
	.type	mult1, %function
mult1:
	mov	r12, sp
	sub	sp, sp, #8
	str	r12, [sp, #4]
	str	lr, [sp, #0]
	ldr	lr, [sp, #0]
	ldr	sp, [sp, #4]
	mov	pc, lr
