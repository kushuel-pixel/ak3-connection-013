// Compare exact metric balls to bracket the distance to the original step-18 state.
#include "packed.hpp"

struct Ball {
    Index index;
    std::vector<uint8_t> depths;
    explicit Ball(const Model& model,State root,int radius) {
        index.add(root);
        depths.push_back(0);
        size_t first=0, last=1;
        for(int d=1;d<=radius;++d) {
            for(size_t i=first;i<last;++i)
                model.each(index.states[i],[&](int,State w){index.add(w);});
            first=last;last=index.states.size();
            depths.resize(last,d);
        }
    }
};

int main(int argc,char**argv) {
    if(argc!=5) {std::cerr<<"usage: prefix endpoints.tsv cap left_radius right_radius\n";return 2;}
    std::ifstream input(argv[1]);
    std::string u,v; std::vector<State> endpoints;
    while(input>>u>>v) endpoints.push_back(pack(encode(u),encode(v),v.size()));
    if(endpoints.size()!=2) return 2;
    Model model{std::stoi(argv[2])};
    int l=std::stoi(argv[3]),r=std::stoi(argv[4]);
    if(model.cap<22||model.cap>28||l<0||l>12||r<0||r>12) return 2;
    Ball left(model,endpoints[0],l),right(model,endpoints[1],r);
    std::vector<uint64_t> hits(l+r+1,0);
    for(Id i=0;i<left.index.states.size();++i) {
        Id j=right.index.find(left.index.states[i]);
        if(j!=missing) ++hits[left.depths[i]+right.depths[j]];
    }
    std::cout<<"{\"cap\":"<<model.cap<<",\"radii\":["<<l<<","<<r<<"],\"sizes\":["<<left.index.states.size()<<","<<right.index.states.size()<<"],\"hits_by_distance_sum\":[";
    for(size_t d=0;d<hits.size();++d) std::cout<<(d?",":"")<<hits[d];
    std::cout<<"]}"<<std::endl;
}
