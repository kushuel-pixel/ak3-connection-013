// Independent COMPUTE055: string equality; normalized-class FNV partitions.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>
#include <sys/resource.h>
static constexpr char alphabet[4]={'X','Y','x','y'};
bool letter(char c){return c=='X'||c=='Y'||c=='x'||c=='y';}
char opposite(char c){return char(c^32);}
std::string canonical(const char* raw,int n){
 if(n<0||n>63)throw std::runtime_error("raw length guard");
 char st[64];int top=0;
 for(int i=0;i<n;i++){char c=raw[i];if(!letter(c))throw std::runtime_error("alphabet");if(top&&st[top-1]==opposite(c))--top;else st[top++]=c;}
 int lo=0,hi=top;while(hi-lo>1&&st[lo]==opposite(st[hi-1])){++lo;--hi;}
 int m=hi-lo;if(m==0)return {};
 // Compare two candidate rotations, skipping an entire equal-prefix block.
 int i=0,j=1,k=0;
 while(i<m&&j<m&&k<m){char a=st[lo+(i+k)%m],b=st[lo+(j+k)%m];
  if(a==b){++k;continue;}
  if(a<b){j+=k+1;if(j==i)++j;}else{i+=k+1;if(i==j)++i;}k=0;
 }
 int at=std::min(i,j);std::string ans;ans.reserve(m);
 for(int x=0;x<m;x++)ans.push_back(st[lo+(at+x)%m]);return ans;
}
std::string normal(const std::string& s){return canonical(s.data(),int(s.size()));}
uint64_t fixed_hash(const std::string& s){uint64_t h=14695981039346656037ULL;for(unsigned char c:s){h^=c;h*=1099511628211ULL;}return h;}
std::string image(const std::string& a,const std::string& b,const char* u,int n){
 char raw[64];int top=0;for(char c:a)raw[top++]=c;for(int i=0;i<n;i++)raw[top++]=u[i];for(char c:b)raw[top++]=c;for(int i=n-1;i>=0;i--)raw[top++]=opposite(u[i]);
 return canonical(raw,top);
}
template<class Visitor>uint64_t enumerate(int B,Visitor visitor){
 if(B<0||B>15)throw std::runtime_error("B guard");char u[16];uint64_t count=0;
 auto visit=[&](auto&& self,int n)->void{visitor(u,n);++count;if(n==B)return;for(char c:alphabet)if(n==0||u[n-1]!=opposite(c)){u[n]=c;self(self,n+1);}};
 visit(visit,0);return count;
}
void limits(){rlimit a{},c{};if(getrlimit(RLIMIT_AS,&a)||getrlimit(RLIMIT_CPU,&c)||a.rlim_cur!=4294967296ULL||a.rlim_max!=4294967296ULL||c.rlim_cur!=90||c.rlim_max!=91)throw std::runtime_error("limits");}
int main(int argc,char**argv){try{
 if(argc==2&&std::string(argv[1])=="--normal-batch"){std::string s;while(std::getline(std::cin,s))std::cout<<normal(s)<<'\n';return 0;}
 if(argc==3&&std::string(argv[1])=="--list"){int B=std::stoi(argv[2]);if(B>6)throw std::runtime_error("list guard");enumerate(B,[&](const char*u,int n){std::cout<<std::string(u,n)<<'\n';});return 0;}
 if(argc!=4||std::string(argv[1])!="--scan")throw std::runtime_error("usage --scan B partition");
 int B=std::stoi(argv[2]),part=std::stoi(argv[3]);if(B<0||B>15||part<0||part>=3)throw std::runtime_error("scan profile");limits();
 std::string a=normal("XyyyxYYYY"),b=normal("xxYYYYYXyyyyy"),c=normal("Y"),d=normal("xxYXy");
 uint64_t expected=1;for(int n=0;n<B;n++)expected*=3;expected=2*expected-1;
 std::unordered_set<std::string> forward;forward.max_load_factor(0.8f);forward.reserve(size_t(expected/3+16));uint64_t selected_f=0,selected_b=0;
 uint64_t nf=enumerate(B,[&](const char*u,int n){auto w=image(a,b,u,n);if(fixed_hash(w)%3==uint64_t(part)){++selected_f;forward.insert(std::move(w));}});
 std::cerr<<"FORWARD partition="<<part<<" tested="<<nf<<" distinct="<<forward.size()<<'\n';
 std::set<std::string> common;
 uint64_t nb=enumerate(B,[&](const char*u,int n){auto w=image(c,d,u,n);if(fixed_hash(w)%3==uint64_t(part)){++selected_b;if(forward.find(w)!=forward.end())common.insert(w);}});
 if(nf!=expected||nb!=expected)throw std::runtime_error("enumeration count");
 std::cout<<"{\"bound\":"<<B<<",\"partition\":"<<part<<",\"partition_modulus\":3,\"partition_hash\":\"FNV1a64\",\"kind\":\"F\",\"outer_sign\":1,\"target\":\"E0\",\"source_factors\":[\""<<a<<"\",\""<<b<<"\"],\"target_factors\":[\""<<c<<"\",\""<<d<<"\"],\"tested_forward\":"<<nf<<",\"tested_backward\":"<<nb<<",\"selected_forward\":"<<selected_f<<",\"selected_backward\":"<<selected_b<<",\"distinct_forward\":"<<forward.size()<<",\"common_words\":[";
 bool first=true;for(const auto&w:common){if(!first)std::cout<<',';first=false;std::cout<<'"'<<w<<'"';}std::cout<<"]}\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
