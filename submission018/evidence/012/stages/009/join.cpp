// Count exact state intersections by the two BFS depths; export every match.
#define LAYER_HELPERS_ONLY
#include "layers.cpp"
#include <sstream>
int main(int argc,char**argv){
    if(argc!=7){std::cerr<<"join left_directory right_directory left_radius right_radius threads output.tsv\n";return 2;}
    fs::path a=argv[1],b=argv[2];int p=std::stoi(argv[3]),q=std::stoi(argv[4]),threads=std::stoi(argv[5]);
    for(int d=0;d<=p;++d)if(!fs::exists(a/(std::to_string(d)+".done")))return 3;
    for(int d=0;d<=q;++d)if(!fs::exists(b/(std::to_string(d)+".done")))return 3;
    std::array<std::string,buckets> results;
    #pragma omp parallel for num_threads(threads) schedule(dynamic)
    for(int shard=0;shard<buckets;++shard){
        size_t count=0;
        for(int d=0;d<=p;++d)count+=fs::file_size(file(a,d,shard))/8;
        Set seen;seen.init(count+1);std::vector<uint8_t> depths(seen.a.size());
        for(int d=0;d<=p;++d)for(State w:load(file(a,d,shard))){
            auto i=seen.pos(w);
            if(seen.a[i])throw std::runtime_error("repeated left state");
            seen.a[i]=w;depths[i]=d;
        }
        std::ostringstream out;
        for(int d=0;d<=q;++d)for(State w:load(file(b,d,shard))){
            auto i=seen.pos(w);
            if(seen.a[i])out<<unsigned(depths[i])<<'\t'<<d<<'\t'<<w<<'\n';
        }
        results[shard]=out.str();
    }
    std::ofstream out(argv[6]);if(!out)return 3;for(auto& v:results)out<<v;
    out.close();if(!out)return 3;
}
