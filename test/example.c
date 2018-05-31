#include <stdio.h>
#include <string.h>

int main (){
  char* a = "abc";
  char b = a[0];
  char c[10] = {"a", "a"};

  sparrow_print(a);
  sparrow_print(c);
  printf("%c\n", b);
  return 0;
}
