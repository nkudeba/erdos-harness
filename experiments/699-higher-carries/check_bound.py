from math import comb,gcd
import json

def split(n):
    a=n;r=0
    while a%2==0:
        a//=2;r+=1
    g=gcd(a,3)
    m=a//g;c=(2**r)*g;e=gcd(n-1,3);b=(n-1)//e
    return r,c,m,e,b

counts={'factor_checks':0,'coprime_m_implications':0,'coprime_b_implications':0,'localized_pairs':0}
examples=[]
for n in range(8,801,2):
    r,c,m,e,b=split(n)
    A=comb(n,3)
    assert n==c*m and m%2==1 and b%2==1
    assert A%m==0 and A%b==0
    assert e*c*c <= 9*4**r
    counts['factor_checks']+=1
    for j in range(4,n//2+1):
        B=comb(n,j)
        if gcd(m,B)==1:
            assert j%m==0
            counts['coprime_m_implications']+=1
        if gcd(b,B)==1:
            assert j*(j-1)%b==0
            counts['coprime_b_implications']+=1
        # Check the algebraic bound under its two localized divisibility inputs,
        # whether or not the original counterexample condition holds.
        if j%m==0 and j*(j-1)%b==0:
            k=j//m
            assert 1<=k and 2*k<=c
            assert k*(c-k)%b==0
            assert b<=k*(c-k)
            assert 4*(n-1)<=e*c*c
            counts['localized_pairs']+=1
            if len(examples)<8: examples.append([n,j,c,m,b,k])
print(json.dumps({'status':'REDUCTION-OK','purpose':'validate a necessary-condition derivation, not search for counterexamples','even_n_range':[8,800],'counts':counts,'localized_examples':examples,'bound_at_r11':9*4**11//4+1},indent=2))
