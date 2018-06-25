#include <stdio.h>
#include <stdlib.h>

void foo(int x) {
  int a[10];
  unsigned int z = (unsigned int)x;

  sparrow_print(z);
  
  if (z > 0) {
       a[z] = 1; /* x is too big by the C casting rule */
    /* A helpful footprint should be included in z's abstract value,
       hopefully, here! */
  }
}

void call_foo() {
  foo(-1);
}

int main()
{
  call_foo();
  return 0;
   
}

void goo() {
  int x;

  int* a = (int*)malloc(x);	/* x is too small by integer overflow */
}
