import sys
sys.path.insert(0,'research/type-b-eulerian-packet/code')
from eul import *
N=30
A=eulerian_polys_recurrence(N)
B=[ONE]
for n in range(N):
 B.append((ONE+(2*n+1)*X)*B[-1]+2*X*(ONE-X)*B[-1].derivative())
for n in range(2,N+1):
 for k in range(n+1):
  q=sum((comb(k,i)*X**i*B[n-i] for i in range(k+1)),const(0))
  tq=tarski_query(q*A[n].derivative(),A[n],'-inf','+inf')
  if tq!=-(n-1):
   print('FAIL',n,k,'query',tq,'expected',-(n-1),flush=True)
   raise SystemExit
 print('PASSED',n,flush=True)
