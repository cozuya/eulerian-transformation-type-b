"""Exact checks for the common-interlacer proof; no floating-point arithmetic.

Run: python research/derangement/check_refined_cone.py [N, default 14]
Requires python-flint and the unchanged packet's eul.py.
"""
from pathlib import Path
from math import comb
import sys
import json

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'type-b-eulerian-packet/code'))
from eul import ONE, X, fmpq_poly, real_root_multiset_count, tarski_query

N = int(sys.argv[1]) if len(sys.argv) > 1 else 14
ZERO = fmpq_poly([0])
B = [ONE]
for n in range(N):
    B.append((ONE + (2*n+1)*X)*B[n] + 2*X*(ONE-X)*B[n].derivative())
D = [sum(((-1)**j*comb(n,j)*B[n-j] for j in range(n+1)), ZERO) for n in range(N+1)]
P = [[ONE]]
for n in range(1,N+1):
    P.append([X*sum(P[n-1][:j],ZERO)+sum(P[n-1][j:],ZERO) for j in range(n+1)])

def weights(factors):
    result = [ONE]
    for a,b in factors:
        temp = [ZERO]*(len(result)+1)
        for i,c in enumerate(result):
            temp[i] += a*c
            temp[i+1] += b*c
        result = temp
    return result

def trans_input(factors):
    cs = weights([(fmpq_poly([a]),fmpq_poly([b])) for a,b in factors])
    return sum((c[0]*B[j] for j,c in enumerate(cs)),ZERO)

counts = {'B_identity':0, 'DB_identity':0, 'endpoint_cone_identity':0,
          'endpoint_cone_root_count':0, 'endpoint_cone_strict_root_sign':0,
          'DB_recurrence':0, 'refined_series_formula':0}
for n in range(N+1):
    # Independent finite-difference formula for the infinite-series numerator.
    for j in range(n+1):
        pp = fmpq_poly([sum((-1)**h*comb(n+1,h)*(l-h)**j*(l-h+1)**(n-j)
                           for h in range(l+1)) for l in range(n+1)])
        assert pp == P[n][j], (n,j,'refined formula')
        counts['refined_series_formula'] += 1
    for k in range(n+1):
        b = sum((comb(k,j)*B[n-k+j] for j in range(k+1)),ZERO)
        d = sum((comb(k,j)*D[n-k+j] for j in range(k+1)),ZERO)
        h = trans_input([(-1,1)]*(n-k)+[(1,1)]*k)
        wb = weights([(ONE,ONE)]*(n-k)+[(2*ONE-X,-X)]*k)
        wd = weights([(-X,2*ONE-X)]*(n-k)+[(ONE,ONE)]*k)
        wh = weights([(-X,2*ONE-X)]*(n-k)+[(2*ONE-X,-X)]*k)
        for name,power,lhs,ws in [('B',k,b,wb),('DB',n-k,d,wd),('endpoint_cone',n,h,wh)]:
            rhs = sum((c*p for c,p in zip(ws,P[n])),ZERO)
            assert (ONE-X)**power*lhs == rhs, (name,n,k,'identity')
            counts[name+'_identity'] += 1
        assert h.degree() == n
        assert real_root_multiset_count(h) == n
        counts['endpoint_cone_root_count'] += 1
        if n >= 2:
            a = P[n][0]
            assert tarski_query(h*a.derivative(),a,'-inf','+inf') == -(n-1)
            counts['endpoint_cone_strict_root_sign'] += 1
        if n<N:
            nextd = sum((comb(k,j)*D[n+1-k+j] for j in range(k+1)),ZERO)
            rhs = (2*n+1)*X*d + 2*X*(ONE-X)*d.derivative()
            if n>k:
                prevd = sum((comb(k,j)*D[n-1-k+j] for j in range(k+1)),ZERO)
                rhs += 2*(n-k)*X*prevd
            assert nextd == rhs, (n,k,'DB recurrence')
            counts['DB_recurrence'] += 1

print(json.dumps({'N':N,'all_passed':True,'exact_checks':counts,
                  'endpoint_basis_n3':[str(trans_input([(-1,1)]*(3-k)+[(1,1)]*k)) for k in range(4)]},indent=2))
