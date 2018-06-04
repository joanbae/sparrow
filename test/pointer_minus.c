#include<stdio.h>

int main()
{
  char str[] = "Point";
  char *p1 = &str[0];
  char *p2 = &str[3];
  
  char chr = str[(p2-p1)+100];
return 0;
}

/*FN */
