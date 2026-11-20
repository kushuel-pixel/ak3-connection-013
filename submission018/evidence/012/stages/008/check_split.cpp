// Second fixed-split checker: first letter in low bits, inverse letters differ by 2.
// No code, indexing or move implementation is shared with the corridor search.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using U=uint64_t;
U mark(int n){return U(1)<<(2*n);}
int len(U w){return (63-__builtin_clzll(w))/2;}
U read_word(const std::string& s){
    U out=mark(s.size());
    for(size_t i=0;i<s.size();++i){
        auto g=std::string("xyXY").find(s[i]);if(g==std::string::npos)throw std::runtime_error("letter");
        out|=U(g)<<(2*i);
    }
    return out;
}
U inv(U w){
    U dest=1;
    while(w>1){dest=(dest<<2)|((w&3)^2);w>>=2;}
    return dest;
}
U product(U a,U b){
    int n=len(a);
    while(n>0 && b>1 && (((a>>(2*n-2))&3)^2)==(b&3)){--n;b>>=2;}
    return (a&(mark(n)-1))|(b<<(2*n));
}
U state(U a,U b){int n=len(a);return (((a&(mark(n)-1))|(b<<(2*n)))<<5)|n;}

template<class F>void each(U v,int cap,F emit){
    int n=v&31;U joined=v>>5;
    U a=mark(n)|(joined&(mark(n)-1)),b=joined>>(2*n);
    auto edge=[&](U u,U w){if(len(u)+len(w)<=cap)emit(state(u,w));};
    U ai=inv(a),bi=inv(b);
    edge(ai,b);edge(a,bi);
    edge(product(a,b),b);edge(product(a,bi),b);
    edge(a,product(b,a));edge(a,product(b,ai));
    for(int g=0;g<4;++g){
        U s=4+g,t=4+(g^2);
        edge(product(product(s,a),t),b);
        edge(a,product(product(s,b),t));
    }
}
struct Set{
    std::vector<U> slots=std::vector<U>(128);
    size_t size=0;
    size_t position(U w)const{
        U h=w;h^=h>>33;h*=0xff51afd7ed558ccdULL;h^=h>>33;h*=0xc4ceb9fe1a85ec53ULL;h^=h>>33;
        size_t i=h&(slots.size()-1);
        while(slots[i]!=0 && slots[i]!=w)i=(i+1)&(slots.size()-1);
        return i;
    }
    bool has(U w)const{return slots[position(w)]!=0;}
    bool insert(U w){
        if((size+1)*4>slots.size()*3){
            std::vector<U> previous=std::move(slots);slots.assign(previous.size()*2,0);
            for(U x:previous)if(x)slots[position(x)]=x;
        }
        auto i=position(w);if(slots[i])return false;
        slots[i]=w;++size;return true;
    }
};
Set ball(U root,int cap,int radius){
    Set seen;seen.insert(root);std::vector<U> front{root};
    for(int d=1;d<=radius;++d){
        std::vector<U> next;
        for(U v:front)each(v,cap,[&](U w){if(seen.insert(w))next.push_back(w);});
        front.swap(next);
    }
    return seen;
}
int main(int argc,char**argv){
    if(argc!=5)return 2;
    std::ifstream src(argv[1]);std::string u,v;std::vector<U> ends;
    while(src>>u>>v)ends.push_back(state(read_word(u),read_word(v)));
    int cap=std::stoi(argv[2]),l=std::stoi(argv[3]),r=std::stoi(argv[4]);
    if(ends.size()!=2 || cap<22 || cap>29 || l<0 || r<0)return 2;
    Set a=ball(ends[0],cap,l),b=ball(ends[1],cap,r);
    size_t hits=0;
    for(U x:a.slots)if(x && b.has(x))++hits;
    std::cout<<"{\"cap\":"<<cap<<",\"radii\":["<<l<<','<<r<<"],\"sizes\":["<<a.size<<','<<b.size<<"],\"hits\":"<<hits<<"}"<<std::endl;
    return 0;
}
