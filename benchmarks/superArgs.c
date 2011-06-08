#include <stdlib.h>

typedef struct {
	void *a, *b, *c, *d, *e, *f, *g, *h;
} ptrContainer_t;

void *func1(ptrContainer_t *p)
{
	void *x;
	x = NULL == p->a ? p->a :
	    NULL == p->b ? p->b :
	    NULL == p->c ? p->c :
	    NULL == p->d ? p->d :
	    NULL == p->e ? p->e :
	    NULL == p->f ? p->f :
	    NULL == p->g ? p->g :
	    NULL == p->h ? p->h : NULL;
	return x;
}

void *func2(void *a, void *b, void *c, void *d, void *e, void *f, void *g, void *h)
{
	void *x;
	x = NULL == a ? a :
	    NULL == b ? b :
	    NULL == c ? c :
	    NULL == d ? d :
	    NULL == e ? e :
	    NULL == f ? f :
	    NULL == g ? g :
	    NULL == h ? h : NULL;
	return x;
}

int main()
{
	ptrContainer_t p;
	p.a = p.b = p.c = p.d = p.e = p.f = p.g = p.h = NULL;
	func1(&p);
	func2(p.a,p.b,p.c,p.d,p.e,p.f,p.g,p.h);
	return 0;
}
