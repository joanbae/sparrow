#include <string.h>
#include <stdio.h>

typedef struct _charVoid
{
  char charFirst[16];
  void * voidSecond;
  void * voidThird;
} charVoid;

int main()
{
  charVoid s;
  char str[] = "hello world in ocaml";
  int len = strlen(str);
  memcpy (s.charFirst, str, len);
  /* printf("s.charFirst: %s\n",s.charFirst); */
}

