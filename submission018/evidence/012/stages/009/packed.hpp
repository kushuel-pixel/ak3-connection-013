#pragma once
// Exact radius neighborhoods and distances for freely reduced ordered word pairs.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Word = uint64_t;
using State = uint64_t;
using Id = uint32_t;
constexpr Id missing = std::numeric_limits<Id>::max();
constexpr int inverse_move[] = {0,1,3,2,5,4,7,6,9,8,11,10,13,12};

int length(Word a) { return (63-__builtin_clzll(a))/2; }
Word flag(int n) { return Word(1)<<(2*n); }

Word encode(const std::string& s) {
    Word a=1;
    for (char c:s) {
        auto pos=std::string("xXyY").find(c);
        if (pos==std::string::npos || length(a)>=30) throw std::runtime_error("invalid word");
        a=(a<<2)|pos;
    }
    return a;
}

Word inverse(Word a,int n) {
    if (!n) return 1;
    Word z=(a^flag(n))^0x5555555555555555ULL;
    z=((z&0x3333333333333333ULL)<<2)|((z>>2)&0x3333333333333333ULL);
    z=((z&0x0f0f0f0f0f0f0f0fULL)<<4)|((z>>4)&0x0f0f0f0f0f0f0f0fULL);
    return flag(n)|(__builtin_bswap64(z)>>(64-2*n));
}

Word multiply(Word a,Word b,int n) {
    while (a!=1 && n && ((a&3)^1)==((b>>(2*n-2))&3)) {
        a>>=2;
        --n;
    }
    return (a<<(2*n)) | (b&(flag(n)-1));
}

Word conj(Word a,int n,int g) {
    Word t=multiply(4+g,a,n);
    return multiply(t,4+(g^1),1);
}

// Height 30 occupies the unused key band with highest bit 62. Heights
// below it retain the original unsigned key. A reduced length-9 block has
// 4*3^8 = 26244 possible literals, so its 18 raw bits fit into 15 bits.
struct Blocks {
    std::array<uint16_t,1<<18> rank{};
    std::array<uint32_t,26244> literal{};
    Blocks(){
        unsigned count=0;
        for(unsigned z=0;z<rank.size();++z){
            bool reduced=true;
            for(int j=0;j<8;++j)if((((z>>(2*j))^(z>>(2*j+2)))&3)==1){reduced=false;break;}
            if(reduced){rank[z]=count;literal[count++]=z;}
        }
        if(count!=literal.size())throw std::runtime_error("block table");
    }
};
inline const Blocks blocks{};
int block_offset(int m){return m<=21?42:2*(m-9);}
State pack(Word a,Word b,int m) {
    Word joined=(a<<(2*m))|(b&(flag(m)-1));
    if(joined<flag(30))return (joined<<5)|m;
    if(joined>=2*flag(30))throw std::runtime_error("state exceeds 30");
    int k=block_offset(m);
    Word raw=joined^flag(30);
    unsigned code=(raw>>k)&((1u<<18)-1);
    Word compact=((raw>>(k+18))<<(k+15))|(Word(blocks.rank[code])<<k)|(raw&((Word(1)<<k)-1));
    return (Word(1)<<62)|(compact<<5)|m;
}
Word unpack_joined(State state){
    if((state>>62)!=1)return state>>5;
    int k=block_offset(state&31);
    Word compact=(state^(Word(1)<<62))>>5;
    auto code=(compact>>k)&32767;
    if(code>=blocks.literal.size())throw std::runtime_error("invalid compact state");
    Word raw=((compact>>(k+15))<<(k+18))|(Word(blocks.literal[code])<<k)|(compact&((Word(1)<<k)-1));
    return flag(30)|raw;
}
struct Model {
    int cap;
    template<class F> void each(State v,F use) const {
        int m=v&31;
        Word joined=unpack_joined(v), a=joined>>(2*m), b=flag(m)|(joined&(flag(m)-1));
        int n=length(a);
        Word ai=inverse(a,n),bi=inverse(b,m);
        use(0,pack(ai,b,m)); use(1,pack(a,bi,m));
        auto first=[&](int op,Word t){
            if (length(t)+m<=cap) use(op,pack(t,b,m));
        };
        auto second=[&](int op,Word t){
            int k=length(t);
            if (n+k<=cap) use(op,pack(a,t,k));
        };
        first(2,multiply(a,b,m)); first(3,multiply(a,bi,m));
        second(4,multiply(b,a,n)); second(5,multiply(b,ai,n));
        for(int g=0;g<4;++g) {
            if(n<30 || (a&3)==unsigned(g) || ((a>>(2*n-2))&3)==unsigned(g^1))first(6+g,conj(a,n,g));
        }
        for(int g=0;g<4;++g) {
            if(m<30 || (b&3)==unsigned(g) || ((b>>(2*m-2))&3)==unsigned(g^1))second(10+g,conj(b,m,g));
        }
    }
    State step(State v,int wanted) const {
        State result=0;
        each(v,[&](int op,State w){if(op==wanted)result=w;});
        if (!result) throw std::runtime_error("inadmissible replay");
        return result;
    }
};

uint64_t mixed(uint64_t z) {
    z^=z>>30; z*=0xbf58476d1ce4e5b9ULL; z^=z>>27;
    z*=0x94d049bb133111ebULL; return z^(z>>31);
}

class Index {
    std::vector<Id> slots=std::vector<Id>(1024,missing);
    size_t locate(State w) const {
        size_t pos=mixed(w)&(slots.size()-1);
        while(slots[pos]!=missing && states[slots[pos]]!=w) pos=(pos+1)&(slots.size()-1);
        return pos;
    }
    void grow() {
        slots.assign(2*slots.size(),missing);
        for(Id i=0;i<states.size();++i) slots[locate(states[i])]=i;
    }
public:
    std::vector<State> states;
    Id find(State w) const {return slots[locate(w)];}
    Id add(State w) {
        if ((states.size()+1)*10>slots.size()*7) grow();
        size_t pos=locate(w);
        if(slots[pos]==missing) {
            if (states.size()>=missing) throw std::runtime_error("index capacity");
            slots[pos]=states.size();
            states.push_back(w);
        }
        return slots[pos];
    }
};

