#include <stdio.h>
#include <string.h>
#include <stdlib.h>
int main( void)
{
   char *ptr;
   char str[20] = "Hi my name is Joan";
   ptr = strdup(str);

   sparrow_print(ptr);
   printf("%c\n",ptr[0]);
     
   return 0;
}
