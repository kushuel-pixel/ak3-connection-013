#pragma once
// Independent word operations: first letter low, alphabet x,y,X,Y.
namespace alternate {
using U=uint64_t;
U mark(int n){return U(1)<<(2*n);}
int len(U w){return (63-__builtin_clzll(w))/2;}
U flip(U w){
    int n=len(w);if(!n)return 1;U z=w^mark(n);
    z=((z&0x5555555555555555ULL)<<1)|((z>>1)&0x5555555555555555ULL);
    z=((z&0x3333333333333333ULL)<<2)|((z>>2)&0x3333333333333333ULL);
    z=((z&0x0f0f0f0f0f0f0f0fULL)<<4)|((z>>4)&0x0f0f0f0f0f0f0f0fULL);
    return mark(n)|(__builtin_bswap64(z)>>(64-2*n));
}
U inverse(U w){U out=1;while(w>1){out=(out<<2)|((w&3)^2);w>>=2;}return out;}
U prod(U a,U b){
    int n=len(a);while(n && b>1 && (((a>>(2*n-2))&3)^2)==(b&3)){--n;b>>=2;}
    return (a&(mark(n)-1))|(b<<(2*n));
}
struct Model{
    int cap;
    template<class F>void each(State key,F emit)const{
        int m=key&31;U joined=unpack_joined(key);
        U a=flip(joined>>(2*m)),b=flip(mark(m)|(joined&(mark(m)-1)));
        int n=len(a);U ai=inverse(a),bi=inverse(b);
        auto edge=[&](int op,U u,U v){int l=len(v);if(len(u)+l<=cap)emit(op,pack(flip(u),flip(v),l));};
        edge(0,ai,b);edge(1,a,bi);edge(2,prod(a,b),b);edge(3,prod(a,bi),b);
        edge(4,a,prod(b,a));edge(5,a,prod(b,ai));
        const int label[]={0,2,1,3};
        for(int g=0;g<4;++g){
            U s=4+g,t=4+(g^2);
            if(n<30 || (a&3)==unsigned(g^2) || ((a>>(2*n-2))&3)==unsigned(g))
                edge(6+label[g],prod(prod(s,a),t),b);
            if(m<30 || (b&3)==unsigned(g^2) || ((b>>(2*m-2))&3)==unsigned(g))
                edge(10+label[g],a,prod(prod(s,b),t));
        }
    }
};
}
