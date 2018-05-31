/* This is a design related issue. */
/* It gives an segmentation fault in reality, but analyzer doesn't
   create an alarm. */
/* This is because of not restricting a lower bound of a offset to be
   0 when the offeset is negative. */
 
#include <string.h>
#include <stdio.h>

int main()
{
 char a[10] = {0,};
 char b[10] = {0,};
 memcpy(a - 100, b - 100, 105);
 return 0;
}
