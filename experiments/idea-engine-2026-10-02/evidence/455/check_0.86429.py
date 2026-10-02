import numpy as np, time
from sympy import primerange
def tau(z):
    t=0.0; prod=1
    for p in primerange(3,400):
        if p>z: t+=(p-2)*(1-1/p)/prod
        prod*=p
    return t
def one_period(z, V=None):
    S=list(primerange(3,z+1)); M=1
    for p in S: M*=p
    P=np.zeros(M,np.float32)
    for p in S: P[::p]=-np.inf
    W=P.copy() if V is None else V.copy()
    tmp=np.empty(M,np.float32); C=np.empty(M,np.float32)
    for v in range(M-1,0,-1):
        L=next(p for p in S if v%p)-2
        k=(2*v)%M
        C[:]=W
        for it in range(L):
            np.add(C[k:],1,out=tmp[:M-k]); np.add(C[:k],1,out=tmp[M-k:])
            np.maximum(tmp,W,out=tmp); np.add(tmp,P,out=C)
        W,C=C,W
    return M,W
t0=time.time(); M,W1=one_period(17); fin=np.isfinite(W1)
V=W1-W1.max(); M,W2=one_period(17,V); D=(W2-V)[fin]
G=D.max(); print("z=17 bracket: %d <= G <= %d ; rho<=%.6f 1/rho>=%.5f t=%.1f"%(D.min(),G,G/M+tau(17),1/(G/M+tau(17)),time.time()-t0))
