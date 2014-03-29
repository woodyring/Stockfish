
#if defined(GPSFISH) && !defined(_WIN32)
int setup_network(int *pargc, char* argv[]) {
  int argc = *pargv;
  if(argc==2 && !strncmp(argv[1],"tcp:",4)){
    std::string s(&argv[1][4]);
    std::string::iterator it=find(s.begin(),s.end(),':');
    if(it==s.end()){
      cerr << "tcp:hostname:port" << endl;
      exit(1);
    }
    std::string hostname(s.begin(),it),portstr(it+1,s.end());
    int portnum=atoi(portstr.c_str());
    int sock_fd=socket(AF_INET,SOCK_STREAM,0);
    if(sock_fd<0){
      cerr << "failed make socket" << endl;
      exit(1);
    }
    struct sockaddr_in sa;
    sa.sin_family=AF_INET;
    sa.sin_port=htons(portnum);
    struct hostent *host;
    host = gethostbyname(hostname.c_str());
    if (host == 0 ) {
      cerr << "Failed gethostbyname" << endl;
    }
    memcpy(&(sa.sin_addr.s_addr),host->h_addr,host->h_length);
    if(connect(sock_fd,(const sockaddr*)&sa,sizeof(sa))<0){
      cerr << "failed connect" << endl;
      exit(1);
    }
    dup2(sock_fd,0);
    dup2(sock_fd,1);
    argc--;
    using_tcp_connection = true;
  }    
  *pargv = argc;
}
#endif


