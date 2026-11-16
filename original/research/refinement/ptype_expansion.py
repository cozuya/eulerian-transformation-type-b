import sympy as s
from math import comb
x=s.symbols('x')
N=14
A=[s.Integer(1)]
B=[s.Integer(1)]
for n in range(N):
 A.append(s.expand((1+n*x)*A[-1]+x*(1-x)*s.diff(A[-1],x)))
 B.append(s.expand((1+(2*n+1)*x)*B[-1]+2*x*(1-x)*s.diff(B[-1],x)))
for n in range(1,N+1):
 P=[s.Poly(sum(comb(j,i)*(x-1)**i*A[n-i] for i in range(j+1)),x) for j in range(n+1)]
 M=s.Matrix([[p.nth(i) for p in P] for i in range(n+1)])
 for k in range(n+1):
  q=s.Poly(sum(comb(k,i)*x**i*B[n-i] for i in range(k+1)),x)
  v=M.inv()*s.Matrix([q.nth(i) for i in range(n+1)])
  if min(v)<0:
   print('FAIL',n,k,list(v),flush=True)
   raise SystemExit
  if n<=4: print(n,k,list(v),flush=True)
 print('PASSED',n,flush=True)
