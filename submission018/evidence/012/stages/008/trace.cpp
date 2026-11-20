// Recover every predecessor leading to a shortest midpoint, using the exact
// distance spheres. No particular path, suffix or exit is fixed in this step.
#define LAYER_HELPERS_ONLY
#include "layers.cpp"
#include <set>
#include <unordered_set>
std::string letters(Word w){
    std::string s;
    while(w!=1){s.push_back("xXyY"[w&3]);w>>=2;}
    std::reverse(s.begin(),s.end());return s;
}
void export_layer(std::ostream& f,const std::set<State>& layer,int d){
    for(State w:layer){int m=w&31;Word both=w>>5;
        f<<d<<'\t'<<letters(both>>(2*m))<<'\t'<<letters(flag(m)|(both&(flag(m)-1)))<<'\n';
    }
}
std::set<State> previous(const std::set<State>& current,const fs::path& dir,int d,const Model& model){
    std::array<std::unordered_set<State>,buckets> wanted;
    std::array<V,buckets> selected;
    for(State w:current)model.each(w,[&](int,State v){wanted[bucket(v)].insert(v);});
    #pragma omp parallel for num_threads(5) schedule(dynamic)
    for(int b=0;b<buckets;++b)if(!wanted[b].empty()){
        for(State v:load(file(dir,d,b)))if(wanted[b].count(v))selected[b].push_back(v);
    }
    std::set<State> found;for(const auto& bucket:selected)found.insert(bucket.begin(),bucket.end());
    if(found.empty())throw std::runtime_error("absent predecessor");return found;
}
int main(int argc,char**argv){
    if(argc!=7){std::cerr<<"trace left_dir right_dir matches cap left_split output.tsv\n";return 2;}
    fs::path a=argv[1],b=argv[2];std::ifstream match(argv[3]);Model model{std::stoi(argv[4])};
    int split=std::stoi(argv[5]),best=1000,da,ds;State w;std::vector<std::tuple<int,int,State>> hits;
    while(match>>da>>ds>>w){hits.emplace_back(da,ds,w);best=std::min(best,da+ds);}
    if(hits.empty())throw std::runtime_error("no witness in balls");split=std::min(split,best);
    std::set<State> mid;
    for(auto [x,y,s]:hits)if(x==split && x+y==best)mid.insert(s);
    if(mid.empty())throw std::runtime_error("bad split");
    std::ofstream out(argv[6]);export_layer(out,mid,split);
    auto frontier=mid;
    for(int i=split;i>0;--i){frontier=previous(frontier,a,i-1,model);export_layer(out,frontier,i-1);}
    frontier=mid;
    for(int j=best-split;j>0;--j){frontier=previous(frontier,b,j-1,model);export_layer(out,frontier,best-j+1);}
    out.close();if(!out)return 3;
}
