#include <stdio.h>

int main()
{
	int i,sum=0, step;
	char str[1024];
	gets(str);
	sscanf("%d\n",str, &step);
	for(i=0; i < 10000; i+=step) {
		sum += i;
	}
	printf("%d\n",sum);
	return 0;
}
