#include <stdio.h>
#include <string.h>

int main(void)
{
   char first[30] = "the address of google?";  
   char second[10] = "google.com";

   sparrow_print(first);
   sparrow_print(second);
   strcat( first, second);           
   printf( "%s\n", first);
   return 0;
}




