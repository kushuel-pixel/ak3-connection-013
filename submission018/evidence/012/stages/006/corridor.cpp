#include "packed.hpp"

std::vector<int> shortest(const Model& model,const Index& index,Id a,Id b) {
    // One parent move per visited state. Each complete expansion increases one radius by one.
    std::array<std::vector<int8_t>,2> parent;
    std::array<std::vector<Id>,2> front;
    for(int i=0;i<2;++i) {
        Id root=i==0 ? a:b;
        parent[i].assign(index.states.size(),-1);
        parent[i][root]=14;
        front[i].push_back(root);
    }
    Id meet=missing;
    while(meet==missing) {
        int s=front[0].size()<=front[1].size()?0:1;
        if(front[s].empty()) throw std::runtime_error("unconnected seeds");
        std::vector<Id> next;
        for(Id id:front[s]) {
            model.each(index.states[id],[&](int op,State w) {
                Id child=index.find(w);
                if (child==missing || parent[s][child]!=-1) return;
                parent[s][child]=op;
                next.push_back(child);
                if(parent[1-s][child]!=-1 && meet==missing) meet=child;
            });
            if(meet!=missing) break;
        }
        front[s].swap(next);
    }
    std::array<std::vector<int>,2> paths;
    for(int s=0;s<2;++s) {
        Id cur=meet;
        while(parent[s][cur]!=14) {
            int op=parent[s][cur];
            if(op<0) throw std::runtime_error("parent gap");
            paths[s].push_back(s==0?op:inverse_move[op]);
            cur=index.find(model.step(index.states[cur],inverse_move[op]));
        }
    }
    std::reverse(paths[0].begin(),paths[0].end());
    paths[0].insert(paths[0].end(),paths[1].begin(),paths[1].end());
    State v=index.states[a];
    for(int op:paths[0]) v=model.step(v,op);
    if(v!=index.states[b]) throw std::runtime_error("final state mismatch");
    return paths[0];
}

int main(int argc,char**argv) {
    if(argc!=5) {std::cerr<<"usage: corridor dag.tsv cap min_radius max_radius\n";return 2;}
    Model model{std::stoi(argv[2])};
    int lo=std::stoi(argv[3]),hi=std::stoi(argv[4]);
    if(model.cap<22 || model.cap>28 || lo<0 || hi<lo) return 2;
    Index index;
    std::ifstream input(argv[1]); std::string u,v; int depth;
    Id a=missing,b=missing;
    while(input>>depth>>u>>v) {
        if (u.size()+v.size()>22) throw std::runtime_error("seed cap");
        Id id=index.add(pack(encode(u),encode(v),v.size()));
        if(depth==0) a=id;
        if(depth==42) b=id;
    }
    if(a==missing || b==missing) throw std::runtime_error("missing endpoint");
    size_t first=0,last=index.states.size();
    for(int r=0;r<=hi;++r) {
        if(r>=lo) {
            auto path=shortest(model,index,a,b);
            std::cout<<"{\"cap\":"<<model.cap<<",\"radius\":"<<r<<",\"vertices\":"<<last<<",\"distance\":"<<path.size()<<",\"moves\":[";
            for(size_t i=0;i<path.size();++i) std::cout<<(i?",":"")<<path[i];
            std::cout<<"]}"<<std::endl;
        } else std::cerr<<"radius "<<r<<", vertices "<<last<<'\n';
        if(r<hi) {
            for(size_t i=first;i<last;++i) model.each(index.states[i],[&](int,State w){index.add(w);});
            first=last;last=index.states.size();
        }
    }
}
