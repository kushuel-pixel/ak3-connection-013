// Audit exact recorded distance layers in place, with a different word
// arithmetic and a read-only table of the claimed previous/current/next keys.
#define LAYER_HELPERS_ONLY
#define ALTERNATE_WORDS
#include "layers.cpp"
using U=uint64_t;

U reverse_bits(U z){
    z=((z>>1)&0x5555555555555555ULL)|((z&0x5555555555555555ULL)<<1);
    z=((z>>2)&0x3333333333333333ULL)|((z&0x3333333333333333ULL)<<2);
    z=((z>>4)&0x0f0f0f0f0f0f0f0fULL)|((z&0x0f0f0f0f0f0f0f0fULL)<<4);
    return __builtin_bswap64(z);
}
U other_key(U key){
    U w=key>>5;int h=length(w);
    U data=h?reverse_bits(w^flag(h))>>(64-2*h):0;
    return ((flag(h)|data)<<5)|(h-int(key&31));
}
struct Claimed{
    Set table;std::vector<unsigned char> tag;size_t missing=0;
    void insert(const V& keys,int shard,bool is_new){
        for(auto w:keys){
            auto i=table.pos(w);
            if(!w || bucket(w)!=shard || table.a[i])throw std::runtime_error("duplicate or wrong shard");
            table.a[i]=w;tag[i]=is_new;if(is_new)++missing;
        }
    }
    void check(U w){
        auto i=table.pos(w);
        if(table.a[i]!=w)throw std::runtime_error("absent successor");
        if(tag[i]){tag[i]=0;--missing;}
    }
};
int main(int argc,char**argv){
    if(argc!=8 && argc!=9){std::cerr<<"audit_layers endpoints cap side radius folder input_limit threads [first_unchecked_depth]\n";return 2;}
    int cap=std::stoi(argv[2]),side=std::stoi(argv[3]),radius=std::stoi(argv[4]),threads=std::stoi(argv[7]);
    fs::path dir=argv[5];size_t limit=std::stoull(argv[6]);
    int first_unchecked=argc==9?std::stoi(argv[8]):0;
    if(first_unchecked<0 || first_unchecked>radius || cap!=29 || side<0||side>1||radius<0||threads<1||!limit)return 2;
    auto e=endpoints(argv[1]);U root=other_key(e[side]);omp_set_dynamic(0);
    size_t total=0,prev_count=0;
    for(int d=0;d<=radius;++d){
        size_t count=0;for(int b=0;b<buckets;++b){
            auto size=fs::file_size(file(dir,d,b));if(size%8)return 3;
            count+=size/8;
            if(d==0){auto v=load(file(dir,d,b));if(v!=(bucket(root)==b?V{root}:V{}))return 3;}
        }
        size_t recorded=0;std::ifstream done(dir/(std::to_string(d)+".done"));
        if(!(done>>recorded)||recorded!=count)return 3;
        if(d && d>=first_unchecked){
            int passes=1;while(prev_count>limit*passes && passes<buckets)passes*=2;
            using Groups=std::array<V,buckets>;std::vector<Groups> runs(threads);
            for(int pass=0;pass<passes;++pass){
                int first=buckets*pass/passes,end=buckets*(pass+1)/passes;
                std::array<Claimed,buckets> claimed;
                #pragma omp parallel for num_threads(threads) schedule(dynamic)
                for(int b=first;b<end;++b){
                    auto cur=load(file(dir,d-1,b)),next=load(file(dir,d,b));V before;
                    if(d>=2)before=load(file(dir,d-2,b));
                    auto& set=claimed[b];set.table.init(before.size()+cur.size()+next.size()+1);
                    set.tag.resize(set.table.a.size());set.insert(before,b,false);set.insert(cur,b,false);set.insert(next,b,true);
                }
                for(int src=0;src<buckets;++src){
                    auto input=load(file(dir,d-1,src)); constexpr size_t block=262144;
                    for(size_t start=0;start<input.size();start+=block){
                        auto top=std::min(start+block,input.size());
                        #pragma omp parallel num_threads(threads)
                        {
                            auto& r=runs[omp_get_thread_num()];
                            for(int b=first;b<end;++b)r[b].clear();
                            #pragma omp for schedule(static)
                            for(size_t i=start;i<top;++i){
                                low::each(other_key(input[i]),cap,[&](U alt){
                                    U w=other_key(alt);int b=bucket(w);if(b>=first && b<end)r[b].push_back(w);
                                });
                            }
                        }
                        #pragma omp parallel for num_threads(threads) schedule(dynamic)
                        for(int b=first;b<end;++b)for(const auto& r:runs)for(U w:r[b])claimed[b].check(w);
                    }
                }
                for(int b=first;b<end;++b)if(claimed[b].missing)throw std::runtime_error("unreached claimed state");
            }
        }
        total+=count;prev_count=count;
        if(d<first_unchecked)continue;
        std::cout<<"{\"cap\":"<<cap<<",\"side\":"<<side<<",\"depth\":"<<d<<",\"sphere\":"<<count<<",\"ball\":"<<total<<"}"<<std::endl;
    }
}
