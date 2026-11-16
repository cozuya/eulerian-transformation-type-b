"""Exact finite checks for the larger cone in GENERALIZED_CONE.md."""
from pathlib import Path
import sys
import json
from math import comb
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'type-b-eulerian-packet'/'code'))
from eul import (ONE,X,fmpq_poly,real_root_multiset_count,is_squarefree,
                 tarski_query,eulerian_polys_recurrence)

N=16
B=[ONE]
for n in range(N):
    B.append((1+(2*n+1)*X)*B[-1]+2*X*(1-X)*B[-1].derivative())
A=eulerian_polys_recurrence(N)

def image(p):
    return sum((a*B[i] for i,a in enumerate(p.coeffs())),fmpq_poly([0]))

larger_cases=0
db_cases=0
for n in range(1,N+1):
    for j in range(n+1):
        p=(X-1)**(n-j)*(X+1)**j
        f=image(p)
        assert f.degree()==n
        assert is_squarefree(f)
        assert real_root_multiset_count(f)==n
        assert f(0)==p(1)
        if n>=2:
            assert tarski_query(f*A[n].derivative(),A[n],'-inf',0)==-(n-1)
        larger_cases+=1

        q=(X-1)**(n-j)*X**j
        g=image(q)
        direct=sum((comb(j,i)*sum(((-1)**h*comb(n-j+i,h)*B[n-j+i-h]
                                  for h in range(n-j+i+1)),fmpq_poly([0]))
                    for i in range(j+1)),fmpq_poly([0]))
        assert g==direct
        assert is_squarefree(g)
        assert real_root_multiset_count(g)==n
        assert g(0)==(1 if j==n else 0)
        if n>=2:
            assert tarski_query(g*A[n].derivative(),A[n],'-inf',0)==-(n-1)
        db_cases+=1

print(json.dumps({'arithmetic':'exact rational; Sturm and Sturm-Tarski',
                  'n_max':N,'larger_cone_basis_cases':larger_cases,
                  'derangement_basis_cases':db_cases,
                  'all_identity_simple_root_and_common_interlacer_sign_checks_passed':True},indent=2))
