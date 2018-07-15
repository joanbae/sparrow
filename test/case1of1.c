#include <sys/types.h>
#include <dirent.h>
#include <stdio.h>
#include <string.h>

int main()
{
   DIR* dir_info;
   dir_info = opendir(".");
   char name[100];
   
   void *ptr= readdir(dir_info);
   struct dirent *p = (struct dirent *) ptr;
   strncpy(name, p -> d_name, 20);
   
   return 0;
}

//bot-involved는 strncpy에서 발생. p->d_name의 값이 메모리에 없기 때문.

