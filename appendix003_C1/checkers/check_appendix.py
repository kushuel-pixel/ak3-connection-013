#!/usr/bin/env python3
"""Exact small checks for Appendix 003; Python standard library only.

This draft consolidation checker does not invoke Lean or the full B15 scans.
It checks all dual columns, not only sampled entries or stored rank metadata.
"""
from pathlib import Path
from itertools import product
import hashlib, json, time

ROOT=Path(__file__).resolve().parents[1]
def inv(w): return [-a for a in w[::-1]]
def red(w):
    z=[]
    for a in w:
        if z and z[-1]==-a: z.pop()
        else: z.append(a)
    return z
def sub(w,images):
    return red(a for i in w for a in (images[i-1] if i>0 else inv(images[-i-1])))
def normal(word,model):
    # Multiply successive letters on the left; x=t, y=a_0 t^-1.
    phi,psi=model['phi'],model['phi_inverse']
    zero=1-model['index_min']; w=[]; k=0
    for a in word[::-1]:
        if a=='x': w,k=sub(w,phi),k+1
        elif a=='X': w,k=sub(w,psi),k-1
        elif a=='y': w,k=red([zero]+sub(w,psi)),k-1
        elif a=='Y': w,k=sub([-zero]+w,phi),k+1
        else: raise ValueError(a)
    return {'fiber_word':w,'stable_exponent':k}
def inverse_string(w): return w.swapcase()[::-1]
def nf(w):
    s=[]
    for a in w:
        if s and s[-1]==a.swapcase(): s.pop()
        else: s.append(a)
    while len(s)>1 and s[0]==s[-1].swapcase(): s=s[1:-1]
    s=''.join(s)
    return min((s[i:]+s[:i] for i in range(len(s))),default='')

class Ring:
    def __init__(self,r,d,p):
        self.r,self.d,self.p=r,d,p
        self.words=[w for n in range(1,d+1) for w in product(range(r),repeat=n)]
    def plus(self,a,b,scale=1):
        z=dict(a)
        for w,c in b.items():
            c=(z.get(w,0)+scale*c)%self.p
            if c:z[w]=c
            else:z.pop(w,None)
        return z
    def mul(self,a,b):
        z={}
        for u,c in a.items():
            for v,e in b.items():
                if len(u)+len(v)<=self.d:
                    w=u+v; z[w]=(z.get(w,0)+c*e)%self.p
        return {w:c for w,c in z.items() if c}
    def image(self,word):
        z={():1}
        for a in word:
            i=abs(a)-1
            f={():1,(i,):1} if a>0 else {(i,)*n:((-1)**n)%self.p for n in range(self.d+1)}
            z=self.mul(z,f)
        return z
    def monomial(self,w,images):
        z={():1}
        for i in w:z=self.mul(z,images[i])
        return z

def mm(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))
I=((1,0),(0,1)); MINUS=((-1,0),(0,-1))
def matrix_profiles(n):
    result=[]
    for kinds in product('FQ',repeat=n):
        profiles=[]
        for signs in product((-1,1),repeat=n):
            m=I
            for k,s in zip(kinds,signs):m=mm(((1,s),(0,1)) if k=='F' else ((1,0),(s,1)),m)
            if m in (I,MINUS):profiles.append({'signs':list(signs),'product':'I' if m==I else '-I'})
        result.append({'layout':''.join(kinds),'I':sum(p['product']=='I' for p in profiles),'-I':sum(p['product']=='-I' for p in profiles),'profiles':profiles})
    return result

def main():
    started=time.monotonic()
    models=json.loads((ROOT/'data/quotient_models.json').read_text())['models']
    certificates=json.loads((ROOT/'data/dual_certificates.json').read_text())['certificates']
    assert len(certificates)==8
    assert {c['id'] for c in certificates}=={'U%d_%s'%(i,k) for i in range(1,5) for k in ['FQQF','QFFQ']}
    endpoints={'S_first':'XyyyxYYYY','S_second':'xxYYYYYXyyyyy','E0_first':'Y','E0_second':'xxYXy'}
    modelchecks=[]
    for i,m in enumerate(models,1):
        r=m['free_kernel_rank']; phi=m['phi']; psi=m['phi_inverse']
        assert len(phi)==len(psi)==r==m['index_max']-m['index_min']
        assert all(sub(phi[j],psi)==[j+1] and sub(psi[j],phi)==[j+1] for j in range(r))
        assert normal(m['word'],m)=={'fiber_word':[],'stable_exponent':0}
        assert {k:normal(w,m) for k,w in endpoints.items()}==m['endpoint_normal_forms']
        modelchecks.append({'model':'U'+str(i),'rank':r,'inverse_automorphisms':True,'relator_killed':True,'endpoint_normal_forms':True})
    dualchecks=[]
    for c in certificates:
        m=models[c['model_index_1_based']-1]; assert c['word']==m['word']
        assert c['id']=='U%d_%s'%(c['model_index_1_based'],c['kind'])
        assert (c['from'],c['to'])==({'FQQF':('S_second','E0_second'),'QFFQ':('S_first','E0_first')}[c['kind']])
        r,d,p=c['rank'],c['truncation_degree'],c['prime']
        assert r==m['free_kernel_rank']; assert all(p%q for q in range(2,int(p**.5)+1))
        R=Ring(r,d,p); assert len(R.words)==c['unknown_coefficients']
        if 'dual_functional' in c:
            dual={tuple(t['monomial']):t['coefficient']%p for t in c['dual_functional']}
        else:
            low=[w for w in R.words if len(w)<d]
            assert len(low)==len(c['lower_functional_coefficients'])
            dual=dict(zip(low,c['lower_functional_coefficients']))
            fac=c['top_factorization']; assert len(fac['position_roots'])==d
            for w in R.words:
                if len(w)==d:
                    val=fac['multiplier']
                    for base,index in zip(fac['position_roots'],w): val=val*pow(base,index,p)%p
                    dual[w]=val
        assert all(w in R.words for w in dual)
        apply=lambda poly:sum(a*dual.get(w,0) for w,a in poly.items())%p
        W=R.image(m['endpoint_normal_forms'][c['from']]['fiber_word'])
        V=R.image(m['endpoint_normal_forms'][c['to']]['fiber_word'])
        images=[R.plus(R.image(w),{():1},-1) for w in m['phi']]
        rhs=R.plus(V,W,-1); assert apply(rhs)==1
        for H in R.words:
            col=R.plus(R.mul({H:1},W),R.mul(V,R.monomial(H,images)),-1)
            assert apply(col)==0,(c['id'],H)
        dualchecks.append({'id':c['id'],'p':p,'d':d,'columns_checked':len(R.words),'all_column_pairings':0,'rhs_pairing':1})
    classes=json.loads((ROOT/'data/common_classes.json').read_text())
    assert [m['word'] for m in models]==[r['word'] for r in classes['classes']]
    a,b,c,d=classes['factors']; witnesses=[]
    for row in classes['classes']:
        u,v=row['F_witnesses']['u'],row['F_witnesses']['v']; U=row['word']
        assert nf(a+u+b+inverse_string(u))==U==nf(c+v+d+inverse_string(v))
        assert len(U)==row['cyclic_length']<=32 and nf(U)==U
        witnesses.append({'word':U,'length':len(U),'witness_lengths':[len(u),len(v)]})
    four,six=matrix_profiles(4),matrix_profiles(6)
    assert sum(x['I'] for x in four)==28 and sum(x['-I'] for x in four)==0
    assert [x['layout'] for x in four if x['profiles']]==['FFFF','FFQQ','FQQF','QFFQ','QQFF','QQQQ']
    assert sum(x['I'] for x in six)==244 and sum(x['-I'] for x in six)==16
    viable=[x for x in six if x['profiles']];assert len(viable)==22
    removed={'FFFFFF','QQQQQQ','FFFFQQ','FFQQQQ','QQFFFF','QQQQFF'}
    residual=[x for x in viable if x['layout'] not in removed]
    assert len(residual)==16 and sum(x['I'] for x in residual)==156 and sum(x['-I'] for x in residual)==16
    # Exact S10 specialization, with function composition rightmost first.
    x=list(range(10));x[0],x[1],x[2]=1,2,0;x[5],x[7],x[6]=7,6,5
    y=[(i+1)%10 for i in range(10)]
    def pi(a):
        z=[0]*10
        for i,v in enumerate(a):z[v]=i
        return z
    def peval(w):
        z=list(range(10));maps={'x':x,'X':pi(x),'y':y,'Y':pi(y)}
        for ch in w:z=[z[maps[ch][i]] for i in range(10)]
        return z
    def cycles(a):
        seen=set();lens=[]
        for i in range(10):
            if i not in seen:
                j=i;n=0
                while j not in seen:seen.add(j);n+=1;j=a[j]
                lens.append(n)
        return sorted(lens)
    assert peval(endpoints['S_second'])==list(range(10))
    assert cycles(peval(endpoints['S_first']))==[1,1,8]
    assert cycles(peval(endpoints['E0_first']))==[10]
    result={'status':'PASS_DRAFT003_EXACT_CHECKS','elapsed_seconds':round(time.monotonic()-started,3),
      'models':modelchecks,'duals':dualchecks,'total_dual_columns':sum(c['columns_checked'] for c in dualchecks),
      'common_class_witnesses':witnesses,'S10_quotient':True,
      'four_mix_profiles':{'I':28,'-I':0,'viable_layouts':6},
      'six_mix_profiles':{'I':244,'-I':16,'viable_layouts':22,'residual_layouts':16,'residual_I':156,'residual_minus_I':16},
      'full_B15_scans_invoked_by_this_checker':False,'Lean_invoked':False,
      'new_independent_review_of_appendix003':'NOT_PERFORMED'}
    (ROOT/'data/matrix_profiles.json').write_text(json.dumps({'four':four,'six':six},indent=2)+'\n')
    (ROOT/'verification/exact_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
