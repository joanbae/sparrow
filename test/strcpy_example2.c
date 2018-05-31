#include <stdio.h>
#include <string.h>
#include <stdlib.h>
int main( void)
{
   char *ptr;
   char str[20] = "Hi my name is Joan";
   
   char *ptr2 = (char *)malloc(20);
   strcpy(ptr2, str);
   sparrow_print(ptr2);
   printf("%c\n",ptr2[30]);
     
   return 0;
}

/* FP, offset: [0, +oo]을 내면서 FP을 냄.  */

