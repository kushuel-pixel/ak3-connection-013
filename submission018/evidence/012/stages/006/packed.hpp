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
        if (pos==std::string::npos || length(a)>=29) throw std::runtime_error("invalid word");
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

State pack(Word a,Word b,int m) {
    return (((a<<(2*m))|(b&(flag(m)-1)))<<5)|m;
}

struct Model {
    int cap;
    template<class F> void each(State v,F use) const {
        int m=v&31;
        Word joined=v>>5, a=joined>>(2*m), b=flag(m)|(joined&(flag(m)-1));
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
        for(int g=0;g<4;++g) first(6+g,conj(a,n,g));
        for(int g=0;g<4;++g) second(10+g,conj(b,m,g));
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

