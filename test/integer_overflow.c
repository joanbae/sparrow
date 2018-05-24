#include <stdio.h>
#include <stdlib.h>

void foo(int x) {
  int a[10];
  unsigned int z = (unsigned int)x;

  /* sparrow_print(z); */
  
  if (z > 0) {
       a[z] = 1; /* x is too big by the C casting rule */
    /* A helpful footprint should be included in z's abstract value,
       hopefully, here! */
  }
}

void call_foo() {
  foo(-1);
}

/*
void hoo(int x) {
  unsigned int y;
  y = x;
  printf("%d\n", x);
  printf("%u\n", y);
  sparrow_print(x);
  sparrow_print(y);

}
*/

int main()
{
  //hoo(0xFFFFFFFF);

  call_foo();

  /*
  unsigned int Giga = 1024 * 1024 * 1024;
  unsigned int u = 2 * Giga;

  printf("%x\n",u);

  int i = u; // (*)

  printf("%d\n", i);
  */

  return 0;
   
}

void goo() {
  int x;

  int* a = (int*)malloc(x);	/* x is too small by integer overflow */
}
