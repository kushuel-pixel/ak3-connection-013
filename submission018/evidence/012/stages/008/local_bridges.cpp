// Length-unbounded literal search for shortcuts between states of a reference
// geodesic DAG. The two local balls are bounded only by their move counts.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
struct Pair {
    std::string a,b;
    bool operator==(const Pair& v) const {return a==v.a && b==v.b;}
};
struct Hash {
    size_t operator()(const Pair& s) const {
        auto a=std::hash<std::string>{}(s.a),b=std::hash<std::string>{}(s.b);
        return a^(b+0x9e3779b97f4a7c15ULL+(a<<6)+(a>>2));
    }
};
char opp(char c){return c^32;}
std::string inv(const std::string& s){
    std::string t(s.rbegin(),s.rend());for(auto& c:t)c=opp(c);return t;
}
std::string times(const std::string& s,const std::string& t){
    size_t k=0;while(k<s.size() && k<t.size() && s[s.size()-1-k]==opp(t[k]))++k;
    std::string w;w.reserve(s.size()+t.size()-2*k);w.append(s,0,s.size()-k);w.append(t,k);return w;
}
std::string conj(char g,const std::string& w){
    return times(times(std::string(1,g),w),std::string(1,opp(g)));
}
template<class F>void each(const Pair& u,F emit){
    auto ai=inv(u.a),bi=inv(u.b);
    emit(0,{ai,u.b});emit(1,{u.a,bi});
    emit(2,{times(u.a,u.b),u.b});emit(3,{times(u.a,bi),u.b});
    emit(4,{u.a,times(u.b,u.a)});emit(5,{u.a,times(u.b,ai)});
    const std::string letters="xXyY";
    for(int i=0;i<4;++i){emit(6+i,{conj(letters[i],u.a),u.b});emit(10+i,{u.a,conj(letters[i],u.b)});}
}
struct Item{Pair state;uint32_t ops;};
template<class F>size_t ball(const Pair& root,int radius,F visit){
    std::unordered_set<Pair,Hash> seen{root};std::vector<Item> frontier{{root,0}};
    for(int d=0;d<=radius;++d){
        for(const auto& n:frontier)visit(n,d);
        if(d==radius)break;
        std::vector<Item> next;
        for(const auto& n:frontier)each(n.state,[&](int op,Pair v){
            if(seen.insert(v).second)next.push_back({std::move(v),(n.ops<<4)|uint32_t(op)});
        });
        frontier.swap(next);
    }
    return seen.size();
}
struct Front{int cost,source,steps;uint32_t ops;};
struct Seed{int depth;Pair p;};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int l=std::stoi(argv[2]),r=std::stoi(argv[3]);if(l<0||l>7||r<0||r>7)return 2;
    std::vector<Seed> seeds;Seed seed;int full=0;std::ifstream in(argv[1]);
    while(in>>seed.depth>>seed.p.a>>seed.p.b){seeds.push_back(seed);full=std::max(full,seed.depth);}
    if(seeds.empty())return 2;
    std::unordered_map<Pair,Front,Hash> left;
    uint64_t left_count=0,right_count=0;size_t highest=0;
    for(size_t i=0;i<seeds.size();++i)left_count+=ball(seeds[i].p,l,[&](const Item& v,int d){
        highest=std::max(highest,v.state.a.size()+v.state.b.size());
        Front f{seeds[i].depth+d,int(i),d,v.ops};
        auto [it,ins]=left.try_emplace(v.state,f);if(!ins && f.cost<it->second.cost)it->second=f;
    });
    std::cerr<<"indexed "<<left.size()<<" distinct left states\n";
    int best=full;uint64_t improvements=0;
    for(size_t j=0;j<seeds.size();++j)right_count+=ball(seeds[j].p,r,[&](const Item& v,int d){
        highest=std::max(highest,v.state.a.size()+v.state.b.size());
        auto it=left.find(v.state);if(it==left.end())return;
        const auto& f=it->second;int cost=f.cost+d+full-seeds[j].depth;
        if(cost<full)++improvements;
        if(cost<best){best=cost;
            std::cout<<"{\"left_source\":"<<f.source<<",\"right_source\":"<<j<<",\"left_steps\":"<<f.steps
                     <<",\"right_steps\":"<<d<<",\"left_code\":"<<f.ops<<",\"right_code\":"<<v.ops
                     <<",\"cost\":"<<best<<"}"<<std::endl;
        }
    });
    std::cout<<"{\"seeds\":"<<seeds.size()<<",\"left_radius\":"<<l<<",\"right_radius\":"<<r
             <<",\"left_visits\":"<<left_count<<",\"left_unique\":"<<left.size()<<",\"right_visits\":"<<right_count
             <<",\"max_observed_length\":"<<highest<<",\"improving_matches\":"<<improvements<<",\"best\":"<<best<<"}"<<std::endl;
}
