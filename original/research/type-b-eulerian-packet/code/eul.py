"""Exact-arithmetic toolkit written for this audit (independent of the submissions' code).

Everything here is exact: rational polynomials via python-flint (fmpq_poly), my own
signed-remainder (Sturm) sequences, Sturm root counts, Sturm-Tarski sign queries and
bisection root isolation.  No floating point is used for any certified statement.
"""
from fractions import Fraction
from itertools import permutations
from math import comb, factorial

from flint import fmpq, fmpq_poly

X = fmpq_poly([0, 1])
ONE = fmpq_poly([1])


def Q(a, b=1):
    """Rational number as fmpq; accepts ints, Fractions, fmpq."""
    if isinstance(a, Fraction):
        return fmpq(a.numerator, a.denominator) / fmpq(b) if b != 1 else fmpq(a.numerator, a.denominator)
    if isinstance(a, fmpq):
        return a / fmpq(b) if b != 1 else a
    return fmpq(a, b)


def const(c):
    return fmpq_poly([Q(c)])


def sgn(v):
    return (v > 0) - (v < 0)


# ----------------------------------------------------------------- Eulerian data
def eulerian_coeffs_bruteforce(n):
    """Descent-generating coefficients by enumerating S_n (constant term first)."""
    if n == 0:
        return [1]
    co = [0] * n
    for p in permutations(range(n)):
        co[sum(p[i] > p[i + 1] for i in range(n - 1))] += 1
    return co


def eulerian_coeffs_closed_form(n):
    """<n,k> = sum_{j=0..k} (-1)^j C(n+1,j) (k+1-j)^n  (independent of any recurrence)."""
    if n == 0:
        return [1]
    return [sum((-1) ** j * comb(n + 1, j) * (k + 1 - j) ** n for j in range(k + 1)) for k in range(n)]


def eulerian_polys_recurrence(N):
    """A_0..A_N from A_{n+1} = (1+n x) A_n + x(1-x) A_n'."""
    A = [ONE, ONE]
    for n in range(1, N):
        a = A[n]
        A.append(fmpq_poly([1, n]) * a + fmpq_poly([0, 1, -1]) * a.derivative())
    return A


def eulerian_polys_closed_form(N):
    return [fmpq_poly(eulerian_coeffs_closed_form(n)) for n in range(N + 1)]


def cayley_from_A(Aj, j):
    """C_j(z) = (1+z)^(j-1) A_j((z-1)/(z+1)) = sum_k e_k (z-1)^k (z+1)^(j-1-k)."""
    out = fmpq_poly([0])
    zm, zp = fmpq_poly([-1, 1]), fmpq_poly([1, 1])
    co = Aj.coeffs()
    for k, e in enumerate(co):
        out += e * zm ** k * zp ** (j - 1 - k)
    return out


def T(p):
    """T = (z^2-1) D + 2z."""
    return fmpq_poly([-1, 0, 1]) * p.derivative() + fmpq_poly([0, 2]) * p


def cayley_polys(N):
    """C_1..C_N by the T-recurrence (index 0 unused)."""
    C = [None, ONE]
    for j in range(1, N):
        C.append(T(C[j]))
    return C


# ----------------------------------------------------------------- Sturm machinery
def _normalize(p):
    """Divide by a positive rational so coefficients stay small; sign pattern unchanged."""
    if p.is_zero():
        return p
    num = p.numer()          # p = num / denom with denom > 0
    c = num.content()
    if c < 0:
        c = -c
    return fmpq_poly(num) / c


def srem_chain(p0, p1):
    """Signed remainder sequence p0, p1, -rem(p0,p1), ... (last nonzero term = +-gcd)."""
    ch = [_normalize(p0), _normalize(p1)]
    if ch[1].is_zero():
        return ch[:1]
    while True:
        r = ch[-2] % ch[-1]
        if r.is_zero():
            break
        ch.append(_normalize(-r))
    return ch


def _sign_at(p, a):
    """Sign of polynomial p at a; a is fmpq or the strings '-inf' / '+inf'."""
    if a == '+inf':
        return sgn(p.leading_coefficient())
    if a == '-inf':
        return sgn(p.leading_coefficient()) * (-1) ** (p.degree() % 2)
    return sgn(p(a))


def variations(chain, a):
    s = [t for t in (_sign_at(p, a) for p in chain) if t != 0]
    return sum(u != v for u, v in zip(s, s[1:]))


def sturm_chain(p):
    return srem_chain(p, p.derivative())


def count_distinct_real_roots(p, a='-inf', b='+inf', chain=None):
    """Number of DISTINCT real roots of p in (a,b).  Valid for non-squarefree p too,
    provided a and b are not roots of p (asserted for finite endpoints)."""
    if chain is None:
        chain = sturm_chain(p)
    for e in (a, b):
        if e not in ('-inf', '+inf'):
            assert p(e) != 0, 'endpoint is a root'
    return variations(chain, a) - variations(chain, b)


def real_root_multiset_count(p, a='-inf', b='+inf'):
    """Real roots in (a,b) counted WITH multiplicity, via squarefree factorisation by gcds."""
    total = 0
    cur = p
    while cur.degree() > 0:
        total += count_distinct_real_roots(cur, a, b)
        cur = cur.gcd(cur.derivative())
    return total


def is_squarefree(p):
    return p.gcd(p.derivative()).degree() == 0


def coprime(p, q):
    return p.gcd(q).degree() == 0


def tarski_query(g, f, a, b):
    """Sturm-Tarski:  sum over distinct real roots x of f in (a,b) of sign(g(x)).
    Requires f(a), f(b) != 0 for finite endpoints."""
    for e in (a, b):
        if e not in ('-inf', '+inf'):
            assert f(e) != 0, 'endpoint is a root'
    ch = srem_chain(f, f.derivative() * g)
    return variations(ch, a) - variations(ch, b)


def isolate_roots(p, a, b):
    """Disjoint open rational intervals (lo,hi), each containing exactly one root of the
    squarefree polynomial p, covering all roots in (a,b).  a,b finite fmpq, not roots."""
    assert is_squarefree(p)
    assert p(a) != 0 and p(b) != 0
    ch = sturm_chain(p)

    def cnt(lo, hi):
        return variations(ch, lo) - variations(ch, hi)

    out = []
    stack = [(a, b, cnt(a, b))]
    while stack:
        lo, hi, k = stack.pop()
        if k == 0:
            continue
        if k == 1:
            out.append((lo, hi))
            continue
        # split at a point that is not a root
        num, den = 1, 2
        while True:
            mid = lo + (hi - lo) * Q(num, den)
            if p(mid) != 0:
                break
            num, den = num + den, 2 * den + 1
        kl = cnt(lo, mid)
        stack.append((mid, hi, k - kl))
        stack.append((lo, mid, kl))
    out.sort(key=lambda iv: iv[0])
    return out


def refine(p, iv):
    """Halve an isolating interval of squarefree p (endpoints stay non-roots)."""
    lo, hi = iv
    num, den = 1, 2
    while True:
        mid = lo + (hi - lo) * Q(num, den)
        if p(mid) != 0:
            break
        num, den = num + den, 2 * den + 1
    if sgn(p(lo)) != sgn(p(mid)):
        return (lo, mid)
    return (mid, hi)


def merged_root_order(polys, a, b, max_rounds=400):
    """polys: dict label -> squarefree polynomial, pairwise coprime, none vanishing at a,b.
    Returns the list of labels of all their roots in (a,b), in increasing order."""
    labels = list(polys)
    for i, l1 in enumerate(labels):
        for l2 in labels[i + 1:]:
            assert coprime(polys[l1], polys[l2]), f'{l1} and {l2} share a root'
    items = []
    for l in labels:
        for iv in isolate_roots(polys[l], a, b):
            items.append([l, iv])
    for _ in range(max_rounds):
        items.sort(key=lambda t: t[1][0])
        clash = False
        for i in range(len(items) - 1):
            if items[i][1][1] > items[i + 1][1][0]:
                clash = True
                items[i][1] = refine(polys[items[i][0]], items[i][1])
                items[i + 1][1] = refine(polys[items[i + 1][0]], items[i + 1][1])
        if not clash:
            # also handle nested intervals: sorted by lo and no overlap => strictly ordered
            return [l for l, _ in items]
    raise RuntimeError('intervals did not separate')


def frac_str(v):
    return str(v)
