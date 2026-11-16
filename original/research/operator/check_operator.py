"""Exact supplementary checks for PROOF.md, not part of the general proof.

Requires python-flint and the packet's exact Sturm helper eul.py.
Run from any directory. All arithmetic is rational; no numerical roots.
"""
from pathlib import Path
import sys
from math import comb
from itertools import combinations_with_replacement
import json

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'type-b-eulerian-packet' / 'code'))
from eul import (fmpq_poly, Q, ONE, real_root_multiset_count,
                 count_distinct_real_roots, merged_root_order, is_squarefree)

Z = fmpq_poly([0, 1])
W = fmpq_poly([-1, 0, 1])
ZP = Z + 1
ZM = Z - 1

def T(f):
    return 2 * W * f.derivative() + 2 * Z * f

def product_operator(cs):
    f = ONE
    for c in cs:
        f = T(f) + c * f
    return f

def cayley(f, n):
    return sum((c * ZM**j * ZP**(n-j) for j,c in enumerate(f.coeffs())), fmpq_poly([0]))

N = 16
C=[ONE]
B=[ONE]
for n in range(N):
    C.append(T(C[-1]))
    B.append((1+(2*n+1)*Z)*B[-1]+2*Z*(1-Z)*B[-1].derivative())
assert all(C[n]==cayley(B[n],n) for n in range(N+1))

endpoint_count=0
R=2*ONE
for n in range(1,N+1):
    assert product_operator([Q(2)]*n)==ZP*R
    assert product_operator([Q(-2)]*n)==ZM*R
    if n>1:
        assert count_distinct_real_roots(R,Q(-1),Q(1))==n-1
    R=2*W*R.derivative()+4*Z*R
    endpoint_count+=1

cube_cases=0
grid=[Q(-3,2),Q(-1,2),Q(0),Q(1,2),Q(3,2)]
for n in range(1,7):
    for cs in combinations_with_replacement(grid,n):
        f=product_operator(cs)
        assert f.degree()==n
        assert count_distinct_real_roots(f,Q(-1),Q(1))==n
        assert is_squarefree(f)
        cube_cases+=1

constant_interlace_cases=0
for n in range(1,11):
    for a in [Q(1,4),Q(1,2),Q(1),Q(3,2),Q(7,4)]:
        for k in range(1,n+1):
            p=product_operator([Q(0)]*(n-k)+[a]*k)
            assert p==sum((comb(k,j)*a**j*C[n-j] for j in range(k+1)),fmpq_poly([0]))
            assert merged_root_order({'p':p,'C':C[n]},Q(-1),Q(1))==['p','C']*n
            constant_interlace_cases+=1

identity_cases=0
beta={}
for n in range(N+1):
    for k in range(n+1):
        b=sum((comb(k,j)*B[n-j] for j in range(k+1)),fmpq_poly([0]))
        beta[n,k]=sum((comb(k,j)*ZP**j*C[n-j] for j in range(k+1)),fmpq_poly([0]))
        assert beta[n,k]==cayley(b,n)
        assert beta[n,k].degree()==n
        if n:
            assert count_distinct_real_roots(beta[n,k],Q(-1),Q(1))==n
        identity_cases+=1

row_pairs=0
for n in range(1,11):
    for ell in range(n):
        for k in range(ell+1,n+1):
            order=merged_root_order({'k':beta[n,k],'ell':beta[n,ell]},Q(-1),Q(1))
            assert order==['k','ell']*n
            row_pairs+=1

print(json.dumps({
    'arithmetic':'exact rational; Sturm counts and rational root isolation',
    'cayley_operator_identities_n_max':N,
    'endpoint_factorization_cases':endpoint_count,
    'operator_cube_cases':cube_cases,
    'operator_cube_n_max':6,
    'operator_cube_grid':['-3/2','-1/2','0','1/2','3/2'],
    'constant_parameter_interlacing_cases':constant_interlace_cases,
    'constant_parameter_n_max':10,
    'constant_parameter_a_grid':['1/4','1/2','1','3/2','7/4'],
    'basis_identity_and_simple_root_count_cases':identity_cases,
    'basis_identity_and_root_count_n_max':N,
    'strong_row_pair_checks':row_pairs,
    'strong_row_pair_n_max':10,
    'all_checks_passed':True,
},indent=2))
