**PROVED**

# Type B Eulerian transformation: complete proof and exact computation record

Prepared November 14, 2026 (America/Chicago).

## 1. Exact conclusions

Let \(B_0=1\) and
\[
B_{n+1}(x)=(1+(2n+1)x)B_n(x)+2x(1-x)B_n'(x),
\qquad \mathcal B(t^m)=B_m(x).
\]
For \(0\le k\le n\), use exactly the basis images in the prompt:
\[
b(n,k)=\mathcal B(t^{n-k}(1+t)^k)
=\sum_{j=0}^k\binom{k}{j}B_{n-j}(x).
\]
The latter expression equals the prompt's sum after replacing its index by
\(k-j\). The input variable is called \(t\) only to distinguish it from the
output variable \(x\).

**Main theorem.** For every \(n\ge1\), the sequence
\[
\boxed{(b(n,n),b(n,n-1),\ldots,b(n,0))}
\]
is strictly interlacing. Every member has degree \(n\) and simple negative
roots. Consequently, for every nonzero vector of real coefficients
\(c_0,\ldots,c_n\ge0\),
\[
\boxed{\sum_{k=0}^n c_k b(n,k)\text{ has }n\text{ distinct strictly negative roots}.}
\]
The result includes every boundary choice of the coefficients. At \(n=0\)
the output is constant. The all-zero input yields the zero polynomial,
handled separately under the usual convention.

**Larger-cone theorem.** Put
\[
K_n=\operatorname{cone}\{(t-1)^{n-j}(t+1)^j:0\le j\le n\}.
\]
Every nonzero \(p\in K_n\) has \(\mathcal B(p)\) with \(n\) distinct
nonpositive roots. They are all negative if \(p(1)>0\); if \(p(1)=0\),
exactly one is zero. For \(n\ge2\), the ordinary Eulerian polynomial
\(A_n\) strictly interlaces all these images.

**Secondary theorem.** With the exact map \(\mathcal D^B\) in the prompt,
every nonzero nonnegative combination of its basis images has \(n\)
distinct nonpositive roots. It has a zero root exactly when \(c_n=0\).
The reverse-\(k\) secondary row is also an interlacing sequence, with the
common zero of all members except \(d(n,n)=B_n\) permitted. Its full proof
is in `research/derangement/DB_OPERATOR_APPENDIX.md`.

**Packet status correction.** The secondary cone conjecture was already
resolved in the 2025 literature: the later Yan–Liu paper [S3] explicitly
states the full cone result and attributes it to Liu–Yan [S2]. The bounded
search did not identify a published resolution of the main \(\mathcal B\)
statement. This is not a novelty certification.

The proof below is elementary and self-contained for the main strong form
and the larger cone. A separate refined-Eulerian proof is included afterward.
The supplied three-term theorem and its type A audit are not dependencies.
No Lean formalization was performed.

## 2. Self-contained proof of the strong main theorem

### 2.1. Cayley operator

Put x=(z-1)/(z+1), C_n(z)=(z+1)^n B_n(x), and

    T f = 2(z^2-1) f' + 2z f.

Direct substitution in the defining type B recurrence gives C_0=1 and
C_{n+1}=T C_n. For 0<=k<=n,

    beta(n,k)(z)=(z+1)^n b(n,k)(x)
                 =sum_{j=0}^k binom(k,j)(z+1)^j C_{n-j}(z).          (1)

Every beta has degree n and positive leading coefficient, since each summand
has degree n and positive leading coefficient.

### 2.2. Root preservation on (-1,1)

If f has degree d, positive leading coefficient, and d simple roots in (-1,1),
then (T+c)f has d+1 simple roots in (-1,1), strictly interlacing those of f,
for every real -2<c<2.

Indeed, at a root r of f its value is 2(r^2-1)f'(r), the opposite sign of
f'(r). At the endpoints its values are (c-2)f(-1) and (c+2)f(1).
These signs give one zero in each of the d+1 intervals cut out by the roots
of f and the endpoints -1,1. Its degree is d+1 and its leading coefficient
is 2(d+1) times that of f. This also proves that each root is simple.

### 2.3. Independently varying operator parameters

For c=(c_1,...,c_n) in (-2,2)^n define

    F_n(z;c) = product_{i=1}^n (T+c_i) 1.

The operators commute, because each is T plus a constant. Section 2.2 therefore
implies that F_n has n simple roots in (-1,1), written increasingly
lambda_1(c)<...<lambda_n(c). Its derivative in c_j is

    G_j = product_{i != j}(T+c_i)1.

Since F_n=(T+c_j)G_j, the polynomial G_j strictly interlaces F_n. Positive
leading coefficients give G_j(lambda_i)/F_n'(lambda_i)>0. Differentiating
the simple-root equation gives

    partial lambda_i / partial c_j
       = -G_j(lambda_i)/F_n'(lambda_i) < 0.                         (2)

Thus every ordered root strictly decreases when any one constant parameter
increases. The roots extend continuously to the closed parameter cube.

### 2.4. Two endpoint polynomials have a common interior factor

Let P_n(z;a)=(T+a)^n1. For n>=1,

    P_n(z;2)  = (z+1) R_{n-1}(z),
    P_n(z;-2) = (z-1) R_{n-1}(z),                                 (3)

where R_0=2 and

    R_m=2(z^2-1)R_{m-1}'+4z R_{m-1}.

This follows by applying T+2 to (z+1)R and T-2 to (z-1)R: both produce the
same new interior factor. The same sign argument as in Section 2.2, with
endpoint multipliers -4 and 4, shows R_{n-1} has n-1 simple roots in (-1,1).

Write u_1<...<u_n for the roots of P_n(z;2), so u_1=-1. Equation (3) says
the roots of P_n(z;-2) are u_2,...,u_n,1. Let r_1<...<r_n be the roots of
C_n=P_n(z;0). By strict parameter monotonicity (2),

    u_i < r_i < u_{i+1}  (1<=i<n),    u_n<r_n<1.                   (4)

For any c in [0,2)^n with at least one positive coordinate, comparison
with the all-zero and all-two parameter vectors gives

    u_i < lambda_i(c) < r_i.                                      (5)

The lower inequality is strict: first increase every coordinate a small
positive amount while keeping them below 2, then take the monotone limit
to the all-two vector. The upper inequality is strict by increasing one
of the positive coordinates from zero (and monotonicity for the rest).

### 2.5. Substitute a=z+1 only after establishing constant-parameter facts

Let

    F_{n,k}(z;a)=T^(n-k)(T+a)^k1
                =sum_{j=0}^k binom(k,j)a^j C_{n-j}(z).

For a in (0,2), write its ordered roots as lambda_{i,k}(a). For k=0 these
are constant r_i. For k>=1, Section 2.3 shows they strictly decrease with a.
For every fixed a in (0,2), they strictly decrease when k increases:

    lambda_{i,k+1}(a) < lambda_{i,k}(a).                           (6)

Equation (1) gives beta(n,k)(z)=F_{n,k}(z;z+1). Its zeros in (-1,1)
are the solutions of

    z = lambda_{i,k}(z+1).                                        (7)

The left side minus the right side is strictly increasing. For k>=1,
it is negative at u_i (at i=1 use the continuous endpoint value a=0)
and positive at r_i, by (5). Consequently there is exactly one solution
s_{i,k} in (u_i,r_i), for each i. These are all n zeros of beta(n,k).
For k=0, set s_{i,0}=r_i.

Equation (6), evaluated pointwise before solving (7), implies

    s_{i,k+1}<s_{i,k}.                                            (8)

Indeed the increasing function z-lambda_{i,k+1}(z+1) is positive at the
zero of z-lambda_{i,k}(z+1), so its own zero lies to the left.

For k>ell, (4), (5), and (8) now yield, for i<n,

    s_{i,k} < s_{i,ell} <= r_i < u_{i+1} < s_{i+1,k}.
Thus beta(n,k) strictly interlaces beta(n,ell), with beta(n,ell) having the
larger roots. The Cayley map is increasing from (-1,1) onto (-infinity,0),
so the same is true of b(n,k) and b(n,ell).

Hence, for every n>=1,

    (b(n,n), b(n,n-1), ..., b(n,0))

is a strictly interlacing sequence of degree-n polynomials with negative
roots.

### 2.6. The full nonnegative cone

This can be concluded without invoking an external interlacing theorem.
At r_i, beta(n,k)(r_i) has sign (-1)^(n-i) for every k>=1, while
beta(n,0)(r_i)=0. Also beta(n,k)(-1)=C_n(-1)=(-2)^n for every k.

For a nonzero vector c_0,...,c_n>=0, if some c_k>0 with k>=1, the sum
sum_k c_k beta(n,k) has alternating nonzero signs at

    -1, r_1, ..., r_n.

It therefore has n distinct roots in (-1,1), one in each successive
interval. Its degree is exactly n. If only c_0 is positive, the sum is a
positive multiple of C_n and has the same conclusion. Applying the Cayley
map proves the exact requested conjecture, with the stronger conclusion
that every nonzero combination has n distinct strictly negative roots.

For n=0 the output is a nonnegative constant; the zero input is handled
by the usual convention that the zero polynomial is real-rooted.


## 3. Proof of the larger cone and the secondary target



Use T, C_n, F_n(z;c), P_n(z;a), and R_{n-1} as defined and proved in
Sections 2.1–2.4 above. Let the roots of R_{n-1} be

    -1=v_0 < v_1 < ... < v_{n-1} < v_n=1.

The endpoint identities

    P_n(z;2)=(z+1)R_{n-1}(z),
    P_n(z;-2)=(z-1)R_{n-1}(z)

and coordinatewise strict root monotonicity imply the following uniform
bound: for any fixed c in (-2,2)^n, F_n(z;c) has exactly one simple root
in each interval (v_{i-1},v_i), i=1,...,n.

Indeed, its i-th ordered root is strictly between the i-th roots of the
all-two and all-minus-two endpoint polynomials, which are v_{i-1} and v_i.
Thus, at v_i for 1<=i<n,

    sign F_n(v_i;c)=(-1)^(n-i),                                    (1)

independently of the choice of c in the open cube.

For a basis polynomial p_j(t)=(t-1)^(n-j)(t+1)^j, put

    H_j(z)=(z+1)^n B[p_j]((z-1)/(z+1)).

Expanding p_j, and using C_m=T^m1, shows that H_j(z) is obtained by
first forming F_n(z;c) with n-j parameters equal to -(z+1) and j
parameters equal to +(z+1). This statement means substitution AFTER
the product of constant-parameter operators has been evaluated.

For z=v_i in (-1,1), all substituted constants are in (-2,2), so (1)
gives sign H_j(v_i)=(-1)^(n-i), for every j. Therefore every nonzero
nonnegative sum H=sum_j d_j H_j has the same strict signs at all v_i.

The polynomial H has degree at most n. Its endpoint values are

    H(-1)=(-2)^n sum_j d_j,
    H(1)=2^n B[p](0)=2^n p(1)>=0.                                 (2)

Here B_m(0)=1 follows immediately from the defining recurrence, and
p(1)=2^n d_n>=0. The first identity follows by Cayley expansion: only
the degree-n input term remains at z=-1.

The alternating signs at -1,v_1,...,v_{n-1}, together with (2), give
one root in each of the first n-1 open intervals and one root in
(v_{n-1},1] (in the open interval if p(1)>0, at 1 if p(1)=0). There
are n distinct roots and degree at most n, so these are exactly all
the roots and all are simple. The inverse Cayley map sends (-1,1)
to (-infinity,0), and z=1 to x=0. This proves the theorem.

For n=1, the same argument uses only the two endpoint values. For n=0
the assertion reduces to a positive constant. The zero input is separate.

### 3.1. The primary cone is contained in K_n

The original generators are t^(n-k)(t+1)^k. Write

    t = ((t-1)+(t+1))/2.

Expanding t^(n-k) with nonnegative binomial coefficients expresses each
generator as a nonnegative combination of the generators of K_n. Moreover
any nonzero original-cone input has p(1)=sum_k c_k 2^k>0, so all transformed
roots are strictly negative.

### 3.2. The secondary derangement cone reduces to the same result

By its definition on monomials and linearity,

    D^B[p(t)] = B[p(t-1)].

For p(t)=sum_k c_k t^(n-k)(t+1)^k,

    p(t-1)=sum_k c_k(t-1)^(n-k)t^k.

The same identity t=((t-1)+(t+1))/2 gives p(t-1) in K_n. Thus D^B[p]
has n distinct nonpositive roots for every nonzero nonnegative coefficient
vector. Its constant term is p(0)=c_n, so all roots are strictly negative
if c_n>0, and exactly one root is zero if c_n=0.

This establishes the entire secondary cone statement independently of
the already-published result found in the literature search.


### 3.3. Identifying the common interlacer

For the ordinary Eulerian polynomials define
\(C^A_n(z)=(z+1)^{n-1}A_n((z-1)/(z+1))\), \(n\ge1\).
Their defining recurrence gives
\(C^A_{n+1}=(z^2-1)(C^A_n)'+2zC^A_n\), with \(C^A_1=1\).
Comparison with the recurrence for \(R\) in Section 2.4 gives
\[
R_{n-1}=2^n C^A_n.
\]
Thus the fixed separators in the larger-cone proof are exactly the Cayley
images of the roots of \(A_n\), proving the asserted common interlacer.


## 4. Independent refined-Eulerian proof of the main cone

### 4.1. Standard refined Eulerian family

Use `A_0=A_1=1` and the usual ordinary Eulerian polynomials. Define

\[
p_{n,j}(x)=(1-x)^{n+1}\sum_{m\ge0}m^j(m+1)^{n-j}x^m,
\qquad 0\le j\le n.
\tag{1}
\]

The right side initially means a formal power series identity; it is a
polynomial. Equivalently,

\[
p_{n,j}(x)=\sum_{i=0}^{j}\binom ji(x-1)^i A_{n-i}(x).
\tag{2}
\]

Indeed, expand `m^j=((m+1)-1)^j` and use
`A_l(x)/(1-x)^(l+1)=sum_{m>=0}(m+1)^l x^m`, including `l=0`.

The refined family satisfies

\[
p_{n,j}=x\sum_{i<j}p_{n-1,i}+\sum_{i\ge j}p_{n-1,i}.
\tag{3}
\]

Thus `(p_{n,0},...,p_{n,n})` is an interlacing sequence. This is the standard
sum-recurrence preservation lemma; an exact source is Athanasiadis,
*On the real-rootedness of the Eulerian transformation*, arXiv:2302.00754v5,
Lemma 2.2(b) and Example 2.3. Its Equation (4) is (3), and the generating
identity immediately before Proposition 3.2 is (1).

In particular,

\[
p_{n,0}=A_n,\qquad p_{n,n}=xA_n,\qquad
A_n\preceq p_{n,j}\quad (0\le j\le n).
\tag{4}
\]

The ordinary Eulerian polynomial `A_n` has `n-1` simple negative roots, and
`A_{n-1}` strictly interlaces `A_n`. These facts follow directly by evaluating
the recurrence

\[
A_n=(1+(n-1)x)A_{n-1}+x(1-x)A_{n-1}'
\]

at the roots of `A_{n-1}` and checking the two end intervals.

### 4.2. The positive-coefficient identity

For each `n,k`, define the polynomials `W_{n,k,j}(x)` by

\[
\sum_{j=0}^n W_{n,k,j}(x)t^j
=(1+t)^{n-k}(2-x-xt)^k.
\tag{5}
\]

Then the following is a polynomial identity:

\[
\boxed{
(1-x)^k b_{n,k}(x)
=\sum_{j=0}^n W_{n,k,j}(x)p_{n,j}(x).
}
\tag{6}
\]

To prove it, first obtain the type B generating identity

\[
\frac{B_l(x)}{(1-x)^{l+1}}
=\sum_{m\ge0}(2m+1)^l x^m.
\tag{7}
\]

The case `l=0` is a geometric series. Applying `2x d/dx + 1` to the right
side multiplies its coefficient by `2m+1`; on the left, after bringing terms
over a common denominator, this gives exactly the defining recurrence for
`B_{l+1}`. Thus (7) follows inductively from the supplied definition.

Now expand the definition of `b_{n,k}` using (7):

\[
\begin{aligned}
\frac{(1-x)^k b_{n,k}(x)}{(1-x)^{n+1}}
&=\sum_{m\ge0}(2m+1)^{n-k}
       \big((1-x)(2m+1)+1\big)^k x^m\\
&=\sum_{m\ge0}\big((m+1)+m\big)^{n-k}
       \big((2-x)(m+1)-xm\big)^k x^m\\
&=\sum_{j=0}^n W_{n,k,j}(x)
       \sum_{m\ge0}m^j(m+1)^{n-j}x^m.
\end{aligned}
\]

Equation (1) proves (6). These calculations establish a rational-function,
and hence polynomial, identity. No convergent-series evaluation at a negative
number of magnitude greater than one is being used.

For every real `r<0`, all coefficients of
`(1+t)^(n-k)(2-r-rt)^k` are strictly positive. Consequently,

\[
W_{n,k,j}(r)>0\qquad(0\le j\le n).
\tag{8}
\]

### 4.3. Signs at the common interlacer

Let `n>=2` and let `r` be any root of `A_n`. Since `A_n` is simple and
`A_n` interlaces every `p_{n,j}` in the direction (4), positive leading
coefficients give

\[
\frac{p_{n,j}(r)}{A_n'(r)}\le0.
\tag{9}
\]

This sign assertion can also be checked directly from alternating roots:
for equal-degree polynomials the roots of `p_{n,j}` occur to the right of
the corresponding roots of `A_n`; a shared root gives zero. The only member
of degree `n` is `p_{n,n}=xA_n`, which vanishes at `r`.

At least one of (9) is strict. Formula (2) gives

\[
p_{n,1}(r)=(r-1)A_{n-1}(r).
\]

Strict interlacing of `A_{n-1}` and `A_n` gives
`A_{n-1}(r)/A_n'(r)>0`; since `r-1<0`,

\[
\frac{p_{n,1}(r)}{A_n'(r)}<0.
\tag{10}
\]

Apply (6), (8), (9), and (10). Since `(1-r)^k>0`,

\[
\boxed{\frac{b_{n,k}(r)}{A_n'(r)}<0}
\qquad(0\le k\le n).
\tag{11}
\]

Therefore the same strict inequality holds with `b_{n,k}` replaced by any
nonzero nonnegative combination `F_n`.

### 4.4. Root count and boundary cases

Write the roots of `A_n` as `r_1<...<r_{n-1}<0`. Since its leading
coefficient is positive,

\[
\operatorname{sgn}F_n(r_i)=(-1)^{n-i}.
\]

Every `b_{n,k}` has degree `n` and leading coefficient `1`, and its constant
term is `2^k`. Hence `F_n` has positive leading coefficient and positive
constant term. Its signs at `-infinity,r_1,...,r_{n-1},0` alternate.
There is at least one root in each of the `n` disjoint open intervals
determined by these points. Since its degree is `n`, it has exactly one
simple root in each, proving the theorem.

For `n=1`, `F_1=(c_0+2c_1)+(c_0+c_1)x` has its single root strictly negative
when `(c_0,c_1)` is nonzero and nonnegative. For `n=0` it is a nonnegative
constant. The all-zero coefficient vector gives the zero polynomial.



## 5. Computations actually performed

All mathematical computations used exact rational or integer arithmetic.
Root statements were checked with Sturm counts, Sturm–Tarski sign queries,
and rational root isolation; no floating-point root experiment is being
reported as a verification. The independent SymPy check used its own exact
root-count implementation and finite-difference numerators, without the
packet's recurrence or Sturm implementation.

| Script | Actual range and counts | Result |
|---|---|---|
| `research/type-b-eulerian-packet/code/typeB_conjecture_probe.py 18` | All original and secondary basis images and every row pair through n=18; vertical interlacing; all four displayed recurrences | All true; this is a fresh rerun, with output in `research/root/logs/packet_probe_n18.txt` |
| `research/refinement/ptype_expansion.py` | 19 cases evaluated; 18 successful before first failure n=5,k=4 | Proposed constant-nonnegative expansion fails; see below |
| `research/refinement/common_a_interlacer.py` | Every 2<=n<=30 and 0<=k<=n; 493 reciprocal common-interlacer sign queries | Passed |
| `research/refinement/identity_and_sign_check.py` | n=0..12: 91 refined generating identities and 91 main-map identities; n=2..12: 88 strict sign queries and 88 multiplicity-aware root counts | Passed |
| `research/operator/check_operator.py` | 17 Cayley identities; 16 endpoint factorizations; 461 parameter multisets for n<=6; 275 constant-parameter interlacing checks for n<=10; 153 basis identities/root counts through n=16; 220 row pairs through n=10 | Passed |
| `research/operator/check_generalized_cone.py` | n=1..16: all 152 larger-cone basis images and all 152 secondary basis images; simple roots, signs and identities | Passed |
| `research/derangement/check_refined_cone.py` | n=0..14: 120 each of main identity, secondary identity, larger-cone identity, larger-cone root count, refined-series identity; 117 strict sign queries; 105 secondary recurrences | Passed |
| `research/root/check_sympy_independent.py` | n=0..8: 45 refined numerator identities, 45 larger-cone identities, 45 constant checks; n=1..8: 44 distinct-root checks | Passed |

These ranges are corroboration. None is used to replace an all-degree lemma.
Complete code and actual stdout are preserved in this bundle. The supplied
three-term checker was inspected but **not rerun**; its preexisting output is
preserved only as part of the original packet and is not claimed as a check
performed in this attempt.

### Failed exploratory assertion

The attempted expansion of the reciprocal basis polynomial into the ordinary
refined family with **constant nonnegative** coefficients fails at n=5,k=4.
The exact coefficient vector is

```
[1, 107/20, 1267/120, -13/120, 881/60, 16]
```

That is a counterexample to an intermediate proposal, not to the problem.
The successful identity instead has polynomial weights that are strictly
positive at every negative test point.

One checker-development failure was also recorded: an initial SymPy
comparison treated `Poly(1,x,domain='QQ')` and `Poly(1,x,domain='ZZ')` as
unequal. The exact difference was zero. Both domains were then set to QQ;
the mathematical formula and assertion were unchanged. The original error,
diagnostic, and correction are in `research/root/logs/checker_development.txt`.

### Additional vertical result

`research/root/LIFT_LEMMA.md` proves the packet's statement (L) independently,
using a positive-residue bound at x=1. This is not required for the strong
operator proof. It involved no additional computation beyond the existing
n<=18 probe.

## 6. Packet audit and prior art

### Packet audit

- The main definitions and indexing have been preserved. All binomial sums
  using B_(n-j) are exactly reindexings of the prompt's sums.
- The Cayley conjugation was rederived, and the four main recurrences were
  freshly checked through n=18. The proof rederives the root-preservation
  facts it needs.
- The packet's description of the secondary problem as unresolved is stale:
  [S2] and [S3] treat it, and [S3]'s indexed introduction explicitly states
  the full nonnegative-cone result and interlacing refinement.
- No algebraic error was found in the packet facts used here. The long type A
  three-term proof and its type B transfer were not prerequisites and are
  not certified by this report.

### Bounded prior-art search

The search checked the stated source, exact titles and phrases for type B
Eulerian/derangement transformations, and the identified 2025 follow-ups.
The publisher abstracts and indexed introductions for [S2] and [S3] were
available; direct full-page opens returned 403, so their detailed proofs
were not inspected. The main and secondary proofs above do not depend on
any uninspected result in those papers.

A more general 2025 work, [S4], was also checked at its transformation
theorems. Its Chow-Eulerian maps and input bases are not simply identified
with the exact main map by its theorem statement. No such identification
is assumed here. The bounded search found no direct published resolution
of the exact main statement; no assertion of novelty is made.

### Sources

- **[S1]** Christos A. Athanasiadis, *On the real-rootedness of the Eulerian
  transformation*, arXiv:2302.00754v5, February 18, 2025. Remark 7.2(b) is
  the target. Lemma 2.2(b), Example 2.3, and the generating identity before
  Proposition 3.2 supply the established refined family used only in the
  alternative proof. https://arxiv.org/html/2302.00754v5
- **[S2]** Lily Li Liu and Xue Yan, *Some interlacing properties related to
  the Eulerian and derangement polynomials*, Advances in Applied Mathematics
  162 (2025), 102776. https://doi.org/10.1016/j.aam.2024.102776
- **[S3]** Xue Yan and Lily Li Liu, *Some interlacing sequences related to
  the Eulerian and derangement polynomials*, Discrete Mathematics 348(11)
  (2025), 114598. https://doi.org/10.1016/j.disc.2025.114598
- **[S4]** Petter Brändén and Lorenzo Vecchi, *Chow polynomials of totally
  nonnegative matrices and posets*, arXiv:2509.17852v3, November 10, 2025,
  especially Section 4.3. https://arxiv.org/pdf/2509.17852

## 7. Verbatim mathematical-check outputs


### research/root/logs/packet_probe_n18.txt

```text
{
 "B": {
  "all_basis_images_real_rooted": true,
  "rows_pairwise_interlacing_consistent_direction": true,
  "row(n-1,k)_interlaces_row(n,k)": true,
  "directions_seen_last_rows": [
   [
    16,
    [
     "g<=f"
    ]
   ],
   [
    17,
    [
     "g<=f"
    ]
   ],
   [
    18,
    [
     "g<=f"
    ]
   ]
  ]
 },
 "DB": {
  "all_basis_images_real_rooted": true,
  "rows_pairwise_interlacing_consistent_direction": true,
  "row(n-1,k)_interlaces_row(n,k)": true,
  "directions_seen_last_rows": [
   [
    16,
    [
     "g<=f"
    ]
   ],
   [
    17,
    [
     "g<=f"
    ]
   ],
   [
    18,
    [
     "g<=f"
    ]
   ]
  ]
 },
 "cayley_recurrences": {
  "beta(n,k+1) = beta(n,k) + (1+z) beta(n-1,k)": true,
  "beta(n+1,k) = T_B beta(n,k) - 2k(z^2-1) beta(n-1,k-1)": true
 },
 "x_recurrences": {
  "b(n,k+1) = b(n,k) + b(n-1,k)": true,
  "b(n+1,k) = (1+(2n+1)x) b(n,k) + 2x(1-x) b(n,k)' - 2k x b(n-1,k-1)": true
 },
 "n_max": 18,
 "seconds": 27.1
}
```

### research/refinement/ptype_expansion.out

```text
1 0 [1, 1]
1 1 [1, 2]
PASSED 1
2 0 [1, 2, 1]
2 1 [1, 2, 2]
2 2 [1, 3/2, 4]
PASSED 2
3 0 [1, 3, 3, 1]
3 1 [1, 8/3, 11/3, 2]
3 2 [1, 5/2, 7/2, 4]
3 3 [1, 17/6, 4/3, 8]
PASSED 3
4 0 [1, 4, 6, 4, 1]
4 1 [1, 4, 5, 6, 2]
4 2 [1, 25/6, 11/3, 15/2, 4]
4 3 [1, 13/3, 35/12, 41/6, 8]
4 4 [1, 49/12, 39/8, 5/12, 16]
PASSED 4
FAIL 5 4 [1, 107/20, 1267/120, -13/120, 881/60, 16]
```

### research/refinement/common_a_interlacer.out

```text
PASSED 2
PASSED 3
PASSED 4
PASSED 5
PASSED 6
PASSED 7
PASSED 8
PASSED 9
PASSED 10
PASSED 11
PASSED 12
PASSED 13
PASSED 14
PASSED 15
PASSED 16
PASSED 17
PASSED 18
PASSED 19
PASSED 20
PASSED 21
PASSED 22
PASSED 23
PASSED 24
PASSED 25
PASSED 26
PASSED 27
PASSED 28
PASSED 29
PASSED 30
```

### research/refinement/identity_and_sign_check.out

```text
n=0: 1 refined generating identities, 1 basis identities, 0 common-interlacer and root-count checks passed
n=1: 2 refined generating identities, 2 basis identities, 0 common-interlacer and root-count checks passed
n=2: 3 refined generating identities, 3 basis identities, 3 common-interlacer and root-count checks passed
n=3: 4 refined generating identities, 4 basis identities, 4 common-interlacer and root-count checks passed
n=4: 5 refined generating identities, 5 basis identities, 5 common-interlacer and root-count checks passed
n=5: 6 refined generating identities, 6 basis identities, 6 common-interlacer and root-count checks passed
n=6: 7 refined generating identities, 7 basis identities, 7 common-interlacer and root-count checks passed
n=7: 8 refined generating identities, 8 basis identities, 8 common-interlacer and root-count checks passed
n=8: 9 refined generating identities, 9 basis identities, 9 common-interlacer and root-count checks passed
n=9: 10 refined generating identities, 10 basis identities, 10 common-interlacer and root-count checks passed
n=10: 11 refined generating identities, 11 basis identities, 11 common-interlacer and root-count checks passed
n=11: 12 refined generating identities, 12 basis identities, 12 common-interlacer and root-count checks passed
n=12: 13 refined generating identities, 13 basis identities, 13 common-interlacer and root-count checks passed
PASS totals: refined_generating_identities=91; basis_identities=91; sign_and_root_count_checks=88
```

### research/operator/check_operator.stdout.txt

```text
{
  "arithmetic": "exact rational; Sturm counts and rational root isolation",
  "cayley_operator_identities_n_max": 16,
  "endpoint_factorization_cases": 16,
  "operator_cube_cases": 461,
  "operator_cube_n_max": 6,
  "operator_cube_grid": [
    "-3/2",
    "-1/2",
    "0",
    "1/2",
    "3/2"
  ],
  "constant_parameter_interlacing_cases": 275,
  "constant_parameter_n_max": 10,
  "constant_parameter_a_grid": [
    "1/4",
    "1/2",
    "1",
    "3/2",
    "7/4"
  ],
  "basis_identity_and_simple_root_count_cases": 153,
  "basis_identity_and_root_count_n_max": 16,
  "strong_row_pair_checks": 220,
  "strong_row_pair_n_max": 10,
  "all_checks_passed": true
}
```

### research/operator/check_generalized_cone.stdout.txt

```text
{
  "arithmetic": "exact rational; Sturm and Sturm-Tarski",
  "n_max": 16,
  "larger_cone_basis_cases": 152,
  "derangement_basis_cases": 152,
  "all_identity_simple_root_and_common_interlacer_sign_checks_passed": true
}
```

### research/derangement/check_refined_cone_n14.json

```text
{
  "N": 14,
  "all_passed": true,
  "exact_checks": {
    "B_identity": 120,
    "DB_identity": 120,
    "endpoint_cone_identity": 120,
    "endpoint_cone_root_count": 120,
    "endpoint_cone_strict_root_sign": 117,
    "DB_recurrence": 105,
    "refined_series_formula": 120
  },
  "endpoint_basis_n3": [
    "x^3 + 20*x^2 + 8*x",
    "x^3 + 22*x^2 + 16*x",
    "x^3 + 24*x^2 + 28*x",
    "x^3 + 26*x^2 + 44*x + 8"
  ]
}
```

### research/root/logs/check_sympy_independent.json

```text
{
  "status": "PASS",
  "arithmetic": "exact rational (SymPy)",
  "n_range": [
    0,
    8
  ],
  "counts": {
    "refined_numerator_identities": 45,
    "endpoint_cone_polynomial_identities": 45,
    "endpoint_cone_distinct_real_root_checks": 44,
    "endpoint_cone_constant_checks": 45
  },
  "degree_3_endpoint_cone_outputs": {
    "0": "x**3 + 20*x**2 + 8*x",
    "1": "x**3 + 22*x**2 + 16*x",
    "2": "x**3 + 24*x**2 + 28*x",
    "3": "x**3 + 26*x**2 + 44*x + 8"
  },
  "sympy_version": "1.14.0"
}
```

### research/root/logs/checker_development.txt

```text
The first run of check_sympy_independent.py stopped at its first comparison,
n=0,j=0, before any mathematical check was recorded as passed:

Traceback (most recent call last):
  File "/workspace/scratch/270385060cc4/research/root/check_sympy_independent.py", line 40, in <module>
    assert p == expansion
           ^^^^^^^^^^^^^^
AssertionError

Cause: SymPy polynomial-object equality distinguishes coefficient domains.
The finite-difference numerator was Poly(1,x,domain='QQ'); the expansion was
Poly(1,x,domain='ZZ'). A diagnostic printed:
{'p': "Poly(1, x, domain='QQ')", 'q': "Poly(1, x, domain='ZZ')", 'polynomial_object_equality': False, 'zero_difference': True}

Correction: explicitly create the expansion over QQ as well. No mathematical
formula or assertion was weakened. The final script and complete successful
output are included separately.
```
