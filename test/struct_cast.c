#include <stdio.h>
#include <string.h>

struct parent{
  int a[10];
};

struct children {
  int a[10];
 };

void setNumber(struct parent *parent) {
  parent -> a[100] = 100;
}

int main() {
  struct parent pat = {{0,1,2,3,4}};
  struct children chil = {{0,1,2,3,4}};
  struct parent * p = ((struct parent *)&chil);
  setNumber(p);
  printf("%d\n", p->a[100]);
  return 0;
}

