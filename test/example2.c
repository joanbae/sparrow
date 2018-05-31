#include <stdio.h>
#include <string.h>

int main(){
  char a[10] = "abcde";
  char * b = a;

  printf("%c\n",b[0]);
  sparrow_print(a);
  sparrow_print(b);
  return 0;
}
