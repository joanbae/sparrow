#include <sys/types.h>
#include <dirent.h>
#include <stdio.h>
int main()
{
   DIR* dir_info;
   struct dirent *dir_entry, *dir_entry2;
   dir_info = opendir(".");
   dir_entry = readdir(dir_info);
   dir_entry2 = dir_entry + 10;             //error를 내야하는데 안 내는 케이스
   char *file_name =  dir_entry2 -> d_name;
   
   return 0;
}
