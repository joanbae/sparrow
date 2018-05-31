#include <stdio.h>

int main()
{
   FILE * pFile;
   char mystring [100];
   char * result;
   pFile = fopen ("myfile.txt" , "r");
   if (pFile == NULL) perror ("Error opening file");
   else {
     result = fgets (mystring , 100 , pFile);
     if (result != NULL )
       puts (mystring);
     fclose (pFile);
   }
   printf("the 4rd character: %c\n", result[100]);

  
   return 0;
}
