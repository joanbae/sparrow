#include <stdio.h>
#include <unistd.h>     // getlogin
#include <pwd.h>        // getpwnam
#include <sys/types.h>  // uid_t

int main()
{
   char          *user_name;
   struct passwd *user_pw;

   user_name   = getlogin();           // 로그인 이름 구하기
   user_pw     = getpwnam( user_name); // 로그인 이름으로  사용자 정보 구하기

   printf( "user name      :%sn", user_pw->pw_name  );
   printf( "user id        :%dn", user_pw->pw_uid   );
   printf( "group id       :%dn", user_pw->pw_gid   );
   return 0;
}

//출처 : http://forum.falinux.com/zbxe/index.php?document_srl=408421&mid=C_LIB


