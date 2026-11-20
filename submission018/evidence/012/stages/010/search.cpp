// Expand complete cap-bounded balls until they meet, hit the requested total radius,
// or reach the explicit combined-state budget. Output each completed layer.
#include "packed.hpp"


State literal(const std::string& u,const std::string& v) {
    return pack(encode(u),encode(v),v.size());
}
struct AvoidEdge : Model {
    const State u=literal("xYYYYXyyy","yyxxYX");
    const State v=literal("xYYYYXyyy","yyxxYYYYYXyyy");
    template<class F>void each(State from,F emit)const {
        Model::each(from,[&](int op,State to){
            if((from==u && to==v)||(from==v && to==u))return;
            emit(op,to);
        });
    }
};

struct Side {
    Index index;
    size_t first=0;
    int radius=0;
    explicit Side(State root) {index.add(root);}
    size_t frontier() const {return index.states.size()-first;}
    void expand(const AvoidEdge& model) {
        size_t last=index.states.size();
        for(size_t i=first;i<last;++i) model.each(index.states[i],[&](int,State w){index.add(w);});
        first=last;
        ++radius;
    }
    std::vector<size_t> ends;
    void record() {ends.push_back(index.states.size());}
    int depth(Id id) const {return std::upper_bound(ends.begin(),ends.end(),id)-ends.begin();}
    std::vector<int> back(State v,const AvoidEdge& model) const {
        std::vector<int> ops;
        int d=depth(index.find(v));
        while(d>0) {
            State predecessor=0;int step=-1;
            model.each(v,[&](int op,State w) {
                Id i=index.find(w);
                if(step<0 && i!=missing && depth(i)==d-1) {step=op;predecessor=w;}
            });
            if(step<0) throw std::runtime_error("missing predecessor");
            ops.push_back(step);v=predecessor;--d;
        }
        return ops;
    }
};

int main(int argc,char**argv) {
    if(argc!=5) {std::cerr<<"usage: global endpoints.tsv cap max_sum state_budget\n";return 2;}
    AvoidEdge model{{std::stoi(argv[2])}}; int bound=std::stoi(argv[3]);
    size_t budget=std::stoull(argv[4]); std::ifstream in(argv[1]);
    std::vector<State> ends;std::string u,v;
    while(in>>u>>v)ends.push_back(pack(encode(u),encode(v),v.size()));
    if(ends.size()!=2 || model.cap<22 || model.cap>28) return 2;
    Side left(ends[0]),right(ends[1]); left.record();right.record();
    while(left.radius+right.radius<bound) {
        Side& active=left.frontier()<=right.frontier()?left:right;
        Side& other=&active==&left?right:left;
        if(left.index.states.size()+right.index.states.size()+4*active.frontier()>budget) {
            std::cout<<"{\"status\":\"budget\"}"<<std::endl;return 0;
        }
        active.expand(model);active.record();
        size_t count=0;State meet=0;
        for(size_t i=active.first;i<active.index.states.size();++i) {
            State w=active.index.states[i];
            if(other.index.find(w)!=missing) {++count;if(!meet)meet=w;}
        }
        std::cout<<"{\"cap\":"<<model.cap<<",\"radii\":["<<left.radius<<","<<right.radius<<"],\"sizes\":["<<left.index.states.size()<<","<<right.index.states.size()<<"],\"hits\":"<<count;
        if(meet) {
            auto a=left.back(meet,model),b=right.back(meet,model);
            std::reverse(a.begin(),a.end());for(int& op:a)op=inverse_move[op];
            a.insert(a.end(),b.begin(),b.end());
            State w=ends[0];for(int op:a)w=model.step(w,op);
            if(w!=ends[1] || int(a.size())!=left.radius+right.radius) throw std::runtime_error("bad witness");
            std::cout<<",\"moves\":[";
            for(size_t i=0;i<a.size();++i)std::cout<<(i?",":"")<<a[i];
            std::cout<<"]";
        }
        std::cout<<"}"<<std::endl;
        if(count) break;
    }
}
