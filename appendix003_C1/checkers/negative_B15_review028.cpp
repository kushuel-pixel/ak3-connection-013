// Independently written for review028. No author code is imported or included.
// Exhaustive recursive reduced words; stack/cyclic reduction; Booth rotation.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>
#include <sys/resource.h>
using K=unsigned __int128;
using S=std::vector<unsigned char>;
constexpr char abc[]="XYxy";
S read(const std::string& s){S v; for(char c:s){auto p=std::find(abc,abc+4,c);if(p==abc+4)throw std::runtime_error("letter");v.push_back(p-abc);}return v;}
S invert(S a){std::reverse(a.begin(),a.end());for(auto& c:a)c^=2;return a;}
K canon(const unsigned char* v,int n){
 if(n>63)throw std::runtime_error("input length");
 unsigned char s[64];int t=0;
 for(int q=0;q<n;++q){if(t && (s[t-1]^2)==v[q])--t;else s[t++]=v[q];}
 int a=0,b=t;while(b-a>1 && (s[a]^2)==s[b-1]){++a;--b;}
 int m=b-a;if(!m)return K(1);
 int i=0,j=1,k=0;
 while(i<m&&j<m&&k<m){auto x=s[a+(i+k)%m],y=s[a+(j+k)%m];if(x==y){++k;continue;}if(x>y){i+=k+1;if(i<=j)i=j+1;}else{j+=k+1;if(j<=i)j=i+1;}k=0;}
 K r=1;int p=std::min(i,j);for(int q=0;q<m;++q)r=(r<<2)|s[a+(p+q)%m];return r;
}
K canon(const S& s){return canon(s.data(),s.size());}
std::string show(K k){std::string s;while(k>1){s+=abc[unsigned(k&3)];k>>=2;}if(k!=1)throw std::runtime_error("key");std::reverse(s.begin(),s.end());return s;}
S normalized(const S&s){return read(show(canon(s)));}
K image(const S&a,const S&b,const S&u){unsigned char z[64];int t=0;for(auto c:a)z[t++]=c;for(auto c:u)z[t++]=c;for(auto c:b)z[t++]=c;for(auto p=u.rbegin();p!=u.rend();++p)z[t++]=*p^2;return canon(z,t);}
template<class F> void recurse(S& u,int need,uint32_t packed,F& f){if(!need){f(u,packed);return;}for(unsigned char c=0;c<4;++c)if(u.empty()||(u.back()^2)!=c){u.push_back(c);recurse(u,need-1,(packed<<2)|c,f);u.pop_back();}}
template<class F> uint64_t all(int B,F f){S u;uint64_t count=0;auto g=[&](const S& w,uint32_t packed){++count;f(w,packed);};for(int n=0;n<=B;++n)recurse(u,n,1,g);return count;}
struct Row{K k;uint32_t witness;};
int main(int argc,char**argv){try{
 if(argc==2&&std::string(argv[1])=="--norm-batch"){std::string s;while(std::getline(std::cin,s))std::cout<<show(canon(read(s)))<<'\n';return 0;}
 if(argc==2&&std::string(argv[1])=="--list5"){all(5,[&](const S&,uint32_t w){std::cout<<show(w)<<'\n';});return 0;}
 if(argc!=2)throw std::runtime_error("usage B");int B=std::stoi(argv[1]);if(B<0||B>15)throw std::runtime_error("B range");
 rlimit as{},cpu{};if(getrlimit(RLIMIT_AS,&as)||getrlimit(RLIMIT_CPU,&cpu)||as.rlim_cur!=(1ULL<<32)||as.rlim_max!=(1ULL<<32)||cpu.rlim_cur!=90||cpu.rlim_max!=91)throw std::runtime_error("resource limits");
 auto started=std::chrono::steady_clock::now();
 S A=normalized(read("XyyyxYYYY")),Bword=invert(normalized(read("xxYYYYYXyyyyy"))),C=normalized(read("Y")),D=invert(normalized(read("xxYXy")));
 uint64_t expected=1;for(int q=0;q<B;++q)expected*=3;expected=2*expected-1;
 std::vector<Row> v;v.reserve(expected);auto nf=all(B,[&](const S&u,uint32_t w){v.push_back({image(A,Bword,u),w});});
 std::sort(v.begin(),v.end(),[](const Row&a,const Row&b){return a.k<b.k||(a.k==b.k&&a.witness<b.witness);});
 v.erase(std::unique(v.begin(),v.end(),[](const Row&a,const Row&b){return a.k==b.k;}),v.end());
 std::cerr<<"FORWARD count="<<nf<<" distinct="<<v.size()<<'\n';
 std::map<K,std::pair<uint32_t,uint32_t>> found;
 auto nb=all(B,[&](const S&u,uint32_t w){K k=image(C,D,u);auto p=std::lower_bound(v.begin(),v.end(),k,[](const Row&r,K key){return r.k<key;});if(p!=v.end()&&p->k==k){auto q=found.find(k);if(q==found.end())found.emplace(k,std::make_pair(p->witness,w));else q->second.second=std::min(q->second.second,w);}});
 if(nf!=expected||nb!=expected)throw std::runtime_error("enumeration count");
 std::cout<<"{\"bound\":"<<B<<",\"tested_forward\":"<<nf<<",\"tested_backward\":"<<nb<<",\"distinct_forward\":"<<v.size()<<",\"shared_words\":[";bool first=true;
 for(auto [k,w]:found){if(!first)std::cout<<',';first=false;auto f=show(w.first),b=show(w.second);std::cout<<"{\"word\":\""<<show(k)<<"\",\"forward_outer_conjugator\":\""<<f<<"\",\"backward_outer_conjugator\":\""<<b<<"\",\"min_forward_length\":"<<f.size()<<",\"min_backward_length\":"<<b.size()<<",\"min_simultaneous_bound\":"<<std::max(f.size(),b.size())<<'}';}
 std::cout<<"],\"wall_seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<"}\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
