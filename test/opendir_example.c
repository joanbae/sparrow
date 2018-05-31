#include <stdio.h>
#include <unistd.h>
#include <dirent.h>
#include <string.h>

int main()
{
   DIR            *dir_info;
   struct dirent  *dir_entry;
   char *fileName;
   int length;
   dir_info = opendir(".");              // 현재 디렉토리를 열기
   if ( NULL != dir_info)
   {
     dir_entry = readdir( dir_info);  // 디렉토리 안에 있는 모든 파일과 디렉토리 출력, dir_entry->d_name);
     fileName = dir_entry->d_name;
     closedir(dir_info);
   }

   length = strlen(fileName);
   sparrow_print(fileName);
   sparrwo_print(length);
   printf("%c\n",fileName[length+100]);
   sparrow_print(dir_entry);
   return 0;
}
