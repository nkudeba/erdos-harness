import numpy as np, time
from fractions import Fraction
from sympy import primerange
NEG=-10**9
def period(U,S,M,okr):
    res=np.arange(M)
    for j in range(1,M):
        v=(2*j)%M
        best=U.copy(); cur=res.copy(); alive=okr.copy()&(U>NEG//2); m=0
        while True:
            m+=1; cur=(cur+v)%M; alive&=okr[cur]
            if not alive.any(): break
            src=np.nonzero(alive)[0]
            np.maximum.at(best,cur[src],U[src]+m)
        U=best
    return U
def cert(S,k0,K):
    M=1
    for p in S: M*=p
    okr=np.array([all(r%p for p in S) for r in range(M)])
    U=np.where(okr,0,NEG).astype(np.int64)
    for _ in range(k0): U=period(U,S,M,okr); U=np.where(okr,U,NEG)
    Uk=U.copy(); assert (Uk[okr]>NEG//2).all() and (Uk[okr]>=0).all()
    for _ in range(K): U=period(U,S,M,okr); U=np.where(okr,U,NEG)
    d=(U-Uk)[okr]
    return M, Fraction(int(d.max()),K), int(d.min()), int(Uk[okr].max()-Uk[okr].min())
def E0exact(S, tail=200):
    tot=Fraction(0); mass=Fraction(1); last=None
    for p in primerange(3,tail):
        if p in S: continue
        tot+=mass*(1-Fraction(1,p))*(p-2); mass/=p; last=p
    # tail: remaining mass * E[P-2 | P>last] ; P(v)<= (crude) any prime; bound tail by mass*sum_{p>last} p*prod... <= mass*2*tail
    return tot, mass
for S,k0,K in [((3,5,7),3,3),((3,5,7,11),3,3),((3,5,7,11,13),2,2)]:
    t=time.time()
    M,rho,dmin,rng=cert(S,k0,K)
    e0,mass=E0exact(S)
    kap=(rho+e0)/M
    print(S,"rho_ub",rho,"(min diff/K %s)"%Fraction(dmin,K),"potential range",rng,"E0~%.8f tailmass %.1e"%(float(e0),float(mass)),
          "1/kappa' = %.6f"%float(1/kap),"t",round(time.time()-t,1),flush=True)
