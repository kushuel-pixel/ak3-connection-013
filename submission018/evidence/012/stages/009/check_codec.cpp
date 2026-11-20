#include "packed.hpp"
#include "low_words.hpp"
#include <random>
#include <set>
#include <sstream>
std::string reduce(const std::string& in){
    std::string w;for(char c:in){if(!w.empty() && (w.back()^32)==c)w.pop_back();else w+=c;}return w;
}
std::string inv_text(const std::string& w){std::string s;for(auto it=w.rbegin();it!=w.rend();++it)s+=(*it^32);return s;}
using P=std::pair<std::string,std::string>;
P text_step(P p,int op){
    auto [a,b]=p;if(op<2){if(op==0)a=inv_text(a);else b=inv_text(b);}
    else if(op<6){if(op<4)a=reduce(a+(op==2?b:inv_text(b)));else b=reduce(b+(op==4?a:inv_text(a)));}
    else{auto& w=op<10?a:b;char c=std::string("xXyY")[(op-6)%4];w=reduce(c+w+char(c^32));}
    return {a,b};
}
std::string decode(Word w){std::string s;while(w>1){s+="xXyY"[w&3];w>>=2;}std::reverse(s.begin(),s.end());return s;}
P decode_pair(State x){int m=x&31;Word u=unpack_joined(x);return {decode(u>>(2*m)),decode(flag(m)|(u&(flag(m)-1)))};}
std::string random_word(std::mt19937& rng,int n){
    std::string s;while(int(s.size())<n){char c="xXyY"[rng()%4];if(s.empty()||s.back()!=(c^32))s+=c;}return s;
}
int main(){
    std::mt19937 rng(20261120);size_t count=0,moves=0;
    for(int cap:{29,30})for(int h=0;h<=cap;++h)for(int m=0;m<=h;++m)for(int k=0;k<45;++k){
        P p={random_word(rng,h-m),random_word(rng,m)};
        State code=pack(encode(p.first),encode(p.second),m);
        if(decode_pair(code)!=p || ((code>>62)==1)!=(h==30))return 2;
        std::array<State,14> got{};Model{cap}.each(code,[&](int op,State s){got[op]=s;});
        std::array<State,14> other{};alternate::Model{cap}.each(code,[&](int op,State s){other[op]=s;});
        if(other!=got)return 5;
        for(int op=0;op<14;++op){
            auto w=text_step(p,op);
            if(w.first.size()+w.second.size()>unsigned(cap)){if(got[op])return 3;}
            else if(!got[op]||decode_pair(got[op])!=w)return 4;
            ++moves;
        }
        ++count;
    }
    std::cout<<"{\"pairs\":"<<count<<",\"label_checks\":"<<moves<<",\"result\":\"PASS\"}\n";
}
