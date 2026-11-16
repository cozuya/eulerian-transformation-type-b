"""Exact finite evidence for Athanasiadis, arXiv:2302.00754v5, Remark 7.2(b) (type B).  NOT a proof.

b(n,k)  = B-transform of x^(n-k)(1+x)^k = sum_i C(k,i) B_{n-k+i}(x)          (degree n)
d(n,k)  = D^B-transform of the same, D^B(x^m) = sum_j (-1)^j C(m,j) B_{m-j}(x)
For each family and every n <= NMAX (argv[1], default 14) this checks, exactly:
  * every b(n,k) is real-rooted
  * each row is pairwise interlacing in ONE consistent direction ("g<=f" printed below means
    b(n,j) interlaces b(n,i) for all i<j, i.e. larger k has the smaller roots)
    -> every nonnegative combination of the row is real-rooted (the conjecture, for that n)
  * b(n-1,k) and b(n,k) interlace
and for the B family the recurrences
  b(n,k+1) = b(n,k) + b(n-1,k)
  b(n+1,k) = (1+(2n+1)x) b(n,k) + 2x(1-x) b(n,k)' - 2k x b(n-1,k-1)
and their Cayley forms for beta(n,k) = (1+z)^n b(n,k)((z-1)/(z+1)).
"""
import sys, json, time
from fractions import Fraction
from math import comb
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from eul import *

t0 = time.time()
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 14
B = [ONE]
for n in range(NMAX + 2):
    B.append(fmpq_poly([1, 2*n+1]) * B[n] + 2 * fmpq_poly([0, 1, -1]) * B[n].derivative())
XP1 = fmpq_poly([1, 1])

def bnk(n, k):          # B-transform of x^(n-k) (1+x)^k
    return sum((comb(k, i) * B[n-k+i] for i in range(k+1)), fmpq_poly([0]))
def dB(m):              # D^B(x^m) = sum (-1)^j C(m,j) B_{m-j}
    return sum(((-1)**j * comb(m, j) * B[m-j] for j in range(m+1)), fmpq_poly([0]))
def dnk(n, k):
    return sum((comb(k, i) * dB(n-k+i) for i in range(k+1)), fmpq_poly([0]))

def relation(f, g):
    """Return 'f<=g' if f interlaces g (g has the larger roots), 'g<=f', 'both', or None."""
    if f.is_zero() or g.is_zero(): return 'both'
    for p in (f, g):
        if p.degree() > 0 and real_root_multiset_count(p) != p.degree(): return None
    d = f.gcd(g)
    f1, g1 = (f // d if d.degree() > 0 else f), (g // d if d.degree() > 0 else g)
    if f1.degree() <= 0 and g1.degree() <= 0: return 'both'
    if not (is_squarefree(f1) or f1.degree() <= 0) or not (is_squarefree(g1) or g1.degree() <= 0): return None
    polys = {}
    if f1.degree() > 0: polys['f'] = f1
    if g1.degree() > 0: polys['g'] = g1
    bnd = Q(2) + max(max(abs(cc) / abs(p.leading_coefficient()) for cc in p.coeffs()) for p in polys.values())
    order = merged_root_order(polys, -bnd, bnd)
    if any(order[i] == order[i+1] for i in range(len(order)-1)): return None
    return 'f<=g' if order[-1] == 'g' else 'g<=f'

out = {}
for name, fam in (('B', bnk), ('DB', dnk)):
    ok_real = ok_seq = ok_lift = True
    detail = []
    for n in range(1, NMAX + 1):
        row = [fam(n, k) for k in range(n+1)]
        for p in row:
            if p.degree() > 0 and real_root_multiset_count(p) != p.degree(): ok_real = False
        dirs = set()
        for i in range(n+1):
            for j in range(i+1, n+1):
                r = relation(row[i], row[j])
                dirs.add(r)
        if None in dirs or ('f<=g' in dirs and 'g<=f' in dirs): ok_seq = False
        detail.append((n, sorted(str(x) for x in dirs)))
        if n >= 2:
            prev = [fam(n-1, k) for k in range(n)]
            for k in range(n):
                if relation(prev[k], row[k]) is None: ok_lift = False
    out[name] = {'all_basis_images_real_rooted': ok_real, 'rows_pairwise_interlacing_consistent_direction': ok_seq,
                 'row(n-1,k)_interlaces_row(n,k)': ok_lift, 'directions_seen_last_rows': detail[-3:]}

# Cayley-side recurrences for beta_{n,k} = (1+z)^n * bnk(n,k)((z-1)/(z+1))
def cay(p, deg):
    o = fmpq_poly([0]); zm, zp = fmpq_poly([-1, 1]), fmpq_poly([1, 1])
    for k, e in enumerate(p.coeffs()): o += e * zm**k * zp**(deg-k)
    return o
beta = {(n, k): cay(bnk(n, k), n) for n in range(0, NMAX + 1) for k in range(n+1)}
W = fmpq_poly([-1, 0, 1]); Z = fmpq_poly([0, 1]); ZP = fmpq_poly([1, 1])
rec1 = all(beta[(n, k+1)] == beta[(n, k)] + ZP * beta[(n-1, k)] for n in range(1, NMAX+1) for k in range(n))
rec2 = all(beta[(n+1, k)] == 2*W*beta[(n, k)].derivative() + 2*Z*beta[(n, k)] - (2*k*W*beta[(n-1, k-1)] if k >= 1 else 0)
           for n in range(1, NMAX) for k in range(n+1))
out['cayley_recurrences'] = {'beta(n,k+1) = beta(n,k) + (1+z) beta(n-1,k)': rec1,
                             'beta(n+1,k) = T_B beta(n,k) - 2k(z^2-1) beta(n-1,k-1)': rec2}
X1 = fmpq_poly([0, 1]); QX = fmpq_poly([0, 1, -1])
recx1 = all(bnk(n, k+1) == bnk(n, k) + bnk(n-1, k) for n in range(1, NMAX+1) for k in range(n))
recx2 = all(bnk(n+1, k) == fmpq_poly([1, 2*n+1])*bnk(n, k) + 2*QX*bnk(n, k).derivative() - (2*k*X1*bnk(n-1, k-1) if k >= 1 else 0)
            for n in range(1, NMAX) for k in range(n+1))
out['x_recurrences'] = {'b(n,k+1) = b(n,k) + b(n-1,k)': recx1,
                        "b(n+1,k) = (1+(2n+1)x) b(n,k) + 2x(1-x) b(n,k)' - 2k x b(n-1,k-1)": recx2}
out['n_max'] = NMAX; out['seconds'] = round(time.time()-t0, 1)
print(json.dumps(out, indent=1))
