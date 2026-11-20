// Independent final intersection: radix-sort each complete bucket on both
// sides and merge by full state value. No membership hash is used in the join.
#include <array>
#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
#include <string>
namespace fs=std::filesystem;
using U=uint64_t;using V=std::vector<U>;
V ball(const fs::path& dir,int radius,int shard){
    V result;
    for(int d=0;d<=radius;++d){
        auto file=dir/(std::to_string(d)+"_"+std::to_string(shard)+".bin");
        auto size=fs::file_size(file);
        if(!fs::exists(dir/(std::to_string(d)+".done"))||size%8)throw std::runtime_error("incomplete layer");
        size_t at=result.size();result.resize(at+size/8);
        std::ifstream in(file,std::ios::binary);if(size && !in.read(reinterpret_cast<char*>(result.data()+at),size))throw std::runtime_error("read");
    }
    return result;
}
void radix(V& x){
    V tmp(x.size());std::vector<size_t> offsets(65536);
    for(int shift=0;shift<64;shift+=16){
        std::fill(offsets.begin(),offsets.end(),0);
        for(U w:x)++offsets[(w>>shift)&65535];
        size_t s=0;for(auto& k:offsets){auto n=k;k=s;s+=n;}
        for(U w:x)tmp[offsets[(w>>shift)&65535]++]=w;
        x.swap(tmp);
    }
    if(std::adjacent_find(x.begin(),x.end())!=x.end())throw std::runtime_error("duplicate state");
}
int main(int argc,char**argv){
    if(argc!=6)return 2;
    std::array<V,64> matches;
    int l=std::stoi(argv[3]),r=std::stoi(argv[4]),threads=std::stoi(argv[5]);size_t left=0,right=0,hits=0;
    #pragma omp parallel for num_threads(threads) schedule(dynamic) reduction(+:left,right,hits)
    for(int b=0;b<64;++b){
        V x=ball(argv[1],l,b),y=ball(argv[2],r,b);radix(x);radix(y);left+=x.size();right+=y.size();
        size_t i=0,j=0;
        while(i<x.size() && j<y.size()){
            if(x[i]<y[j])++i;
            else if(x[i]>y[j])++j;
            else{matches[b].push_back(x[i]);++hits;++i;++j;}
        }
    }
    std::cout<<"{\"radii\":["<<l<<','<<r<<"],\"sizes\":["<<left<<','<<right<<"],\"hits\":"<<hits<<",\"keys\":[";bool sep=false;
    for(auto& shard:matches)for(auto key:shard){if(sep)std::cout<<',';std::cout<<key;sep=true;}
    std::cout<<"]}\n";
}
