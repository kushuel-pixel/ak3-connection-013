// Stream the outer left layer. A bit filter only avoids writing definite
// misses. Every retained state is checked by exact equality in its right ball.
#define LAYER_HELPERS_ONLY
#include "layers.cpp"
#include "low_words.hpp"
#include <unordered_set>
#ifndef FILTER_BLOCK_BITS
#define FILTER_BLOCK_BITS 28
#endif
constexpr unsigned block_bits=FILTER_BLOCK_BITS;
static_assert(block_bits>=6 && block_bits<=32);
constexpr uint64_t block_mask=(uint64_t(1)<<(block_bits-6))-1;
size_t block_index(uint64_t hash){
    return ((hash>>58)<<(block_bits-6))|(hash&block_mask);
}
uint64_t flags(uint64_t key){
    auto h=mixed(key^0xe2be6549740c1ad7ULL);
    return (1ULL<<(h&63))|(1ULL<<((h>>8)&63))|(1ULL<<((h>>16)&63))|(1ULL<<((h>>24)&63));
}
std::string candidate_file(const fs::path& scratch,int tid,int bucket){
    return (scratch/("c_"+std::to_string(tid)+"_"+std::to_string(bucket)+".bin")).string();
}
int main(int argc,char**argv){
    if(argc!=8){std::cerr<<"stream_join cap A_dir S_dir left_saved_radius right_radius scratch threads\n";return 2;}
    int cap=std::stoi(argv[1]),p=std::stoi(argv[4]),q=std::stoi(argv[5]),threads=std::stoi(argv[7]);
    fs::path a=argv[2],s=argv[3],temp=argv[6];fs::create_directories(temp);
    if(cap<22||cap>30||p<0||q<0||threads<1)return 2;
    for(int d=0;d<=p;++d)if(!fs::exists(a/(std::to_string(d)+".done")))return 3;
    for(int d=0;d<=q;++d)if(!fs::exists(s/(std::to_string(d)+".done")))return 3;
    V filter(uint64_t(1)<<block_bits,0);
    size_t right=0;
    #pragma omp parallel for num_threads(threads) schedule(dynamic) reduction(+:right)
    for(int b=0;b<buckets;++b)for(int d=0;d<=q;++d){
        auto v=load(file(s,d,b));right+=v.size();
        for(State w:v){auto h=mixed(w);if(int(h>>58)!=b)throw std::runtime_error("bucket");
            filter[block_index(h)]|=flags(w);}
    }
    #ifdef LOW_ARITHMETIC
    alternate::Model model{cap};
#else
    Model model{cap};
#endif
    uint64_t left=0,outer_moves=0,candidates=0;
    omp_set_dynamic(0);
    #pragma omp parallel num_threads(threads) reduction(+:left,outer_moves,candidates)
    {
        int tid=omp_get_thread_num();std::array<std::unique_ptr<Stream>,buckets> streams;
        for(int b=0;b<buckets;++b)streams[b]=std::make_unique<Stream>(candidate_file(temp,tid,b),"wb");
        auto visit=[&](State w){
            auto h=mixed(w),mask=flags(w);if((filter[block_index(h)]&mask)!=mask)return;
            int b=h>>58;if(std::fwrite(&w,8,1,streams[b]->f)!=1)throw std::runtime_error("spool");++candidates;
        };
        #pragma omp for schedule(dynamic)
        for(int b=0;b<buckets;++b)for(int d=0;d<=p;++d){
            auto v=load(file(a,d,b));left+=v.size();
            for(State w:v){visit(w);if(d==p)model.each(w,[&](int,State y){++outer_moves;visit(y);});}
        }
        for(auto& stream:streams)stream->close();
    }
    V().swap(filter);
    std::array<std::vector<std::pair<State,int>>,buckets> hits;
    #pragma omp parallel for num_threads(threads) schedule(dynamic)
    for(int b=0;b<buckets;++b){
        std::unordered_set<State> survivor;
        for(int t=0;t<threads;++t)for(State w:load(candidate_file(temp,t,b)))survivor.insert(w);
        for(int d=0;d<=q;++d)for(State w:load(file(s,d,b)))if(survivor.count(w))hits[b].emplace_back(w,d);
    }
    std::cout<<"{\"cap\":"<<cap<<",\"radii\":["<<p+1<<','<<q<<"],\"left_stored_radius\":"<<p
             <<",\"left_stored_ball\":"<<left<<",\"right_ball\":"<<right<<",\"outer_label_visits\":"<<outer_moves
             <<",\"candidate_visits\":"<<candidates<<",\"matches\":[";bool sep=false;
    for(auto& row:hits)for(auto [key,rd]:row){if(sep)std::cout<<',';std::cout<<'['<<key<<','<<rd<<']';sep=true;}
    std::cout<<"]}"<<std::endl;
}
