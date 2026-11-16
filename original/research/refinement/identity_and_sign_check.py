"""Exact verification of the polynomial identity in common_interlacer_proof.md.
Requires python-flint and the supplied eul.py. All calculations are rational.
"""
import sys
from pathlib import Path
from math import comb
root=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(root/'type-b-eulerian-packet/code'))
from eul import X,ONE,const,eulerian_polys_recurrence,tarski_query,real_root_multiset_count
N=12
A=eulerian_polys_recurrence(N)
B=[ONE]
for n in range(N):
 B.append((ONE+(2*n+1)*X)*B[-1]+2*X*(ONE-X)*B[-1].derivative())
identities=0
sign_checks=0
refined_generating_checks=0
for n in range(N+1):
 P=[sum((comb(j,i)*(X-ONE)**i*A[n-i] for i in range(j+1)),const(0)) for j in range(n+1)]
 # Independently recover numerator of sum_{m>=0} m^j(m+1)^(n-j) x^m.
 # Values 0..n determine all numerator coefficients. Formula uses finite differences.
 for j,p in enumerate(P):
  coeff=[sum((-1)**h*comb(n+1,h)*(m-h)**j*(m-h+1)**(n-j) for h in range(m+1)) for m in range(n+1)]
  expected=sum((v*X**i for i,v in enumerate(coeff)),const(0))
  assert p==expected,(n,j,p,expected)
  refined_generating_checks+=1
 for k in range(n+1):
  b=sum((comb(k,i)*B[n-i] for i in range(k+1)),const(0))
  W=[ONE]
  for h in range(n):
   c0,c1=(ONE,ONE) if h<n-k else (2*ONE-X,-X)
   new=[const(0) for _ in range(len(W)+1)]
   for j,w in enumerate(W):
    new[j]+=c0*w
    new[j+1]+=c1*w
   W=new
  rhs=sum((w*p for w,p in zip(W,P)),const(0))
  assert (ONE-X)**k*b==rhs,(n,k)
  identities+=1
  if n>=2:
   assert tarski_query(b*A[n].derivative(),A[n],'-inf','+inf')==-(n-1),(n,k)
   assert real_root_multiset_count(b)==n,(n,k)
   sign_checks+=1
 print(f'n={n}: {n+1} refined generating identities, {n+1} basis identities, {n+1 if n>=2 else 0} common-interlacer and root-count checks passed',flush=True)
print(f'PASS totals: refined_generating_identities={refined_generating_checks}; basis_identities={identities}; sign_and_root_count_checks={sign_checks}',flush=True)
