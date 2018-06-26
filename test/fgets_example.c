#include <stdio.h>
#include <stdlib.h>

char *name;

int main(void){
  int name_size = 100;
  char name[100];
  char *result = fgets(name, name_size, stdin);
  sparrow_print(result);
  char c = name[10];
  sparrow_print(c);
  return 0;
  
}

/* int main(void) */
/* { */
/*   int name_size = 100; */
/*   name = calloc(name_size, sizeof(char)); */
/*   fgets(name, name_size, stdin); */
/*   sparrow_print(name); */
/*   printf("%c\n", name[0]); */
/*   free(name); */
/* } */
