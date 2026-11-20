// Disk-backed exact BFS on a reversible graph. Keep the previous and current
// spheres while constructing the next. Different buckets compare full keys.
#include "packed.hpp"
#include <filesystem>
#include <omp.h>
#include <memory>
#include <cstdio>
namespace fs=std::filesystem;
using V=std::vector<State>;
constexpr int buckets=64;
int bucket(State x){return mixed(x)>>(64-6);}
std::string file(const fs::path& root,int d,int b){
    return (root/(std::to_string(d)+"_"+std::to_string(b)+".bin")).string();
}
struct Stream{
    FILE* f;
    Stream(const std::string& p,const char* mode):f(std::fopen(p.c_str(),mode)){
        if(!f) throw std::runtime_error("open: "+p);
    }
    ~Stream(){if(f) std::fclose(f);}
    void write(const V& v){if(!v.empty() && std::fwrite(v.data(),8,v.size(),f)!=v.size())throw std::runtime_error("write");}
    void close(){if(std::fclose(f))throw std::runtime_error("flush");f=nullptr;}
};
V load(const std::string& p){
    auto n=fs::file_size(p);if(n%8)throw std::runtime_error("bad length");
    V v(n/8);Stream s(p,"rb");
    if(!v.empty() && std::fread(v.data(),8,v.size(),s.f)!=v.size()) throw std::runtime_error("read");
    return v;
}
struct Set{
    V a;size_t used=0;
    void init(size_t expected){size_t n=16;while(n*8<expected*10)n*=2;a.assign(n,0);}
    size_t pos(State x)const{
        size_t i=mixed(x)&(a.size()-1);
        while(a[i]&&a[i]!=x)i=(i+1)&(a.size()-1);
        return i;
    }
    bool add(State x){
        if((used+1)*10>a.size()*8){
            auto old=std::move(a);a.assign(2*old.size(),0);
            for(State w:old)if(w)a[pos(w)]=w;
        }
        auto i=pos(x);if(a[i])return false;a[i]=x;++used;return true;
    }
};
#ifdef ALTERNATE_WORDS
namespace low {
#define main in_memory_split_entry
#include "check_split.cpp"
#undef main
}
struct LayerModel{
    int cap;
    template<class F>void each(State w,F emit)const{low::each(w,cap,[&](State t){emit(-1,t);});}
};
State root_state(const std::string& u,const std::string& v){return low::state(low::read_word(u),low::read_word(v));}
const char* encoding="low-v1 ";
#else
using LayerModel=Model;
State root_state(const std::string& u,const std::string& v){return pack(encode(u),encode(v),v.size());}
const char* encoding="packed-v1 ";
#endif
std::vector<State> endpoints(const char* path){
    std::ifstream in(path);std::string u,v;V e;
    while(in>>u>>v)e.push_back(root_state(u,v));
    if(e.size()!=2)throw std::runtime_error("endpoints");return e;
}
void grow(const fs::path& path,int d,int cap,int passes,int threads){
    LayerModel model{cap};
    constexpr size_t block=262144;
    using Groups=std::array<V,buckets>;
    std::vector<Groups> runs(threads);
    for(int pass=0;pass<passes;++pass){
        int begin=buckets*pass/passes,end=buckets*(pass+1)/passes;
        std::array<Set,buckets> seen;
        std::array<std::unique_ptr<Stream>,buckets> output;
        #pragma omp parallel for num_threads(threads) schedule(dynamic)
        for(int b=begin;b<end;++b){
            auto cur=load(file(path,d,b));V prev;
            if(d>0)prev=load(file(path,d-1,b));
            seen[b].init(prev.size()+cur.size()*3+16);
            for(auto x:prev)seen[b].add(x);
            for(auto x:cur)seen[b].add(x);
            output[b]=std::make_unique<Stream>(file(path,d+1,b),"wb");
        }
        for(int source=0;source<buckets;++source){
            auto input=load(file(path,d,source));
            for(size_t base=0;base<input.size();base+=block){
                size_t top=std::min(base+block,input.size());
                #pragma omp parallel num_threads(threads)
                {
                    auto& r=runs[omp_get_thread_num()];
                    for(int b=begin;b<end;++b)r[b].clear();
                    #pragma omp for schedule(static)
                    for(size_t i=base;i<top;++i)model.each(input[i],[&](int,State w){
                        int b=bucket(w);if(b>=begin && b<end)r[b].push_back(w);
                    });
                }
                #pragma omp parallel for num_threads(threads) schedule(dynamic,1)
                for(int b=begin;b<end;++b){
                    V fresh;
                    for(auto& r:runs)for(State w:r[b])if(seen[b].add(w))fresh.push_back(w);
                    output[b]->write(fresh);
                }
            }
        }
        for(int b=begin;b<end;++b)output[b]->close();
    }
}
#ifndef LAYER_HELPERS_ONLY
int main(int argc,char**argv){
    if(argc!=8){std::cerr<<"layers endpoints cap side radius folder max_input_per_pass threads\n";return 2;}
    auto e=endpoints(argv[1]);int cap=std::stoi(argv[2]),side=std::stoi(argv[3]),radius=std::stoi(argv[4]);
    fs::path dir=argv[5];size_t per=std::stoull(argv[6]);int threads=std::stoi(argv[7]);
    if(side<0||side>1||cap<22||cap>29||radius<0||per==0||threads<1)return 2;
    omp_set_dynamic(0);fs::create_directories(dir);
    // The manifest pins the root and model so a resumed run cannot mix searches.
    auto manifest=dir/"identity.txt";std::string key=encoding+std::to_string(cap)+" "+std::to_string(e[side]);
    if(fs::exists(manifest)){std::ifstream rd(manifest);std::string got;std::getline(rd,got);if(key!=got)throw std::runtime_error("identity");}
    else{std::ofstream w(manifest);w<<key<<'\n';}
    size_t total=0,previous=0;
    for(int d=0;d<=radius;++d){
        auto marker=dir/(std::to_string(d)+".done");
        if(!fs::exists(marker)){
            if(d==0){for(int b=0;b<buckets;++b){Stream out(file(dir,0,b),"wb");if(bucket(e[side])==b)out.write(V{e[side]});out.close();}}
            else{
                int passes=1;while(previous>per*passes && passes<buckets)passes*=2;
                grow(dir,d-1,cap,passes,threads);
            }
        }
        size_t size=0;for(int b=0;b<buckets;++b){auto bytes=fs::file_size(file(dir,d,b));if(bytes%8)throw std::runtime_error("size");size+=bytes/8;}
        if(fs::exists(marker)){std::ifstream done(marker);size_t expected;if(!(done>>expected)||expected!=size)throw std::runtime_error("incomplete layer");}
        else{auto tmp=marker;tmp+=".tmp";{std::ofstream f(tmp);f<<size<<'\n';}fs::rename(tmp,marker);}
        total+=size;previous=size;
        std::cout<<"{\"cap\":"<<cap<<",\"side\":"<<side<<",\"depth\":"<<d<<",\"sphere\":"<<size<<",\"ball\":"<<total<<"}"<<std::endl;
    }
    return 0;
}
#endif
