#include <stdlib.h>
#include <string.h>

int main(){
  char *value = getenv("USER");
  char p[30];
  strncpy(p, value, 10);
  return 0;
}
