#include<stdio.h>

int main()
{
char str[] = "Point";
char *p1 = &str[0];
char *p2 = &str[3];

printf("result: %c",str[p2-p1]);
return 0;
}
