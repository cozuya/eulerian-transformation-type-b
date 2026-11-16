"""Independent exact check using SymPy and finite-difference numerators.

No use of the packet's recurrence or Sturm implementation.  The mathematical
claim is proved in the report; these are finite corroborating checks.
"""
import json
from math import comb
from pathlib import Path

import sympy as sp

x, t, u = sp.symbols("x t u")
N = 8


def numerator(n, f):
    return sp.Poly(sum(
        sum((-1)**j * comb(n + 1, j) * f(h - j)
            for j in range(h + 1)) * x**h
        for h in range(n + 1)), x, domain=sp.QQ)


B = [numerator(n, lambda m, n=n: (2*m + 1)**n)
     for n in range(N + 1)]
A = [numerator(n, lambda m, n=n: (m + 1)**n)
     for n in range(N + 1)]

counts = {"refined_numerator_identities": 0,
          "endpoint_cone_polynomial_identities": 0,
          "endpoint_cone_distinct_real_root_checks": 0,
          "endpoint_cone_constant_checks": 0}
examples = {}

for n in range(N + 1):
    refined = []
    for j in range(n + 1):
        p = numerator(n, lambda m, n=n, j=j: m**j * (m+1)**(n-j))
        expansion = sp.Poly(sum(comb(j, i) * (x-1)**i * A[n-i].as_expr()
                                for i in range(j+1)), x, domain=sp.QQ)
        assert p == expansion
        counts["refined_numerator_identities"] += 1
        refined.append(p)

    for k in range(n + 1):
        source = sp.Poly((t-1)**(n-k) * (t+1)**k, t)
        transformed = sp.Poly(sum(source.nth(i)*B[i].as_expr()
                                  for i in range(n+1)), x)
        weights = sp.Poly((-x+(2-x)*u)**(n-k) * ((2-x)-x*u)**k, u)
        rhs = sum(weights.nth(j)*refined[j].as_expr() for j in range(n+1))
        assert sp.Poly((1-x)**n * transformed.as_expr()-rhs, x).is_zero
        counts["endpoint_cone_polynomial_identities"] += 1
        assert transformed.nth(0) == source.eval(1)
        counts["endpoint_cone_constant_checks"] += 1
        if n:
            assert transformed.degree() == n
            assert transformed.gcd(transformed.diff()).degree() == 0
            assert transformed.count_roots(-sp.oo, sp.oo) == n
            assert transformed.count_roots(0, sp.oo) == (1 if k < n else 0)
            counts["endpoint_cone_distinct_real_root_checks"] += 1
        if n == 3:
            examples[str(k)] = str(transformed.as_expr())

result = {"status": "PASS", "arithmetic": "exact rational (SymPy)",
          "n_range": [0, N], "counts": counts,
          "degree_3_endpoint_cone_outputs": examples,
          "sympy_version": sp.__version__}
print(json.dumps(result, indent=2))
