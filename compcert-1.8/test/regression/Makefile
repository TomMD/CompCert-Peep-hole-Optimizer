include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=-stdlib ../../runtime -dparse -dc -dclight -dasm \
  -fstruct-passing -fstruct-assign -fbitfields

LIBS=$(LIBMATH)

# Can run and have reference output in Results

TESTS=bitfields1 bitfields2 bitfields3 bitfields4 \
  bitfields5 bitfields6 \
  expr1 initializers volatile2 \
  funct3 expr5 struct7 struct8 casts1 casts2

# Other tests: should compile to .s without errors (but expect warnings)
EXTRAS=annot1 commaprec expr2 expr3 expr4 extern1 funct2 funptr1 init1 \
  init2 init3 init4 pragmas ptrs1 ptrs2 sizeof1 struct1 struct2 struct3 \
  struct4 struct5 struct6 types1 volatile1

# Test known to fail
FAILURES=funct1 varargs1

all_s: $(TESTS:%=%.s) $(EXTRAS:%=%.s)

all: $(TESTS:%=%.compcert) $(EXTRAS:%=%.s)

%.compcert: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -o $*.compcert $*.c $(LIBS)

%.s: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -S $*.c

clean:
	rm -f *.compcert
	rm -f *.parsed.c *.compcert.c *.light.c *.s *.o *~ 

test:
	@for i in $(TESTS); do \
	   if ./$$i.compcert | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

