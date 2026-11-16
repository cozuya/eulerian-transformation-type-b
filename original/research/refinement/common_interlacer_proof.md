# A common ordinary-Eulerian interlacer proves the type B cone conjecture

## Statement

Let `B_0=1` and

\[
B_{n+1}(x)=(1+(2n+1)x)B_n(x)+2x(1-x)B_n'(x).
\]

For `0 <= k <= n`, put

\[
b_{n,k}(x)=\sum_{i=0}^k\binom ki B_{n-i}(x).
\]

For every `n >= 1` and every nonzero vector of nonnegative real numbers
`(c_0,...,c_n)`, the polynomial

\[
F_n(x)=\sum_{k=0}^n c_k b_{n,k}(x)
\]

has exactly `n` distinct negative roots. When `n >= 2`, the ordinary Eulerian
polynomial `A_n(x)` strictly interlaces `F_n(x)`. The zero combination and `n=0`
are immediate under the usual real-rootedness convention.

This establishes the exact cone conjecture. It does not, by itself, prove the
ordered pairwise interlacing of the `b_{n,k}`.

## Standard refined Eulerian family

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

## The positive-coefficient identity

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

## Signs at the common interlacer

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

## Root count and boundary cases

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

## Exact computation record

All scripts below are in this directory, and all output is recorded verbatim.

1. `ptype_expansion.py`: attempted a stronger constant-positive-coefficient
   expansion of the reciprocal basis in the `p_{n,j}`. This fails at
   `(n,k)=(5,4)`: the expansion vector is
   `[1,107/20,1267/120,-13/120,881/60,16]`. The output file is
   `ptype_expansion.out`. This failed attempt is distinct from (6), whose
   coefficients depend on `x` and are positive only where needed (`x<0`).
2. `common_a_interlacer.py`: exact Sturm–Tarski queries for the reciprocal
   basis `sum_i binom(k,i) x^i B_{n-i}`, for every `2<=n<=30` and `0<=k<=n`.
   All 493 queries returned `-(n-1)`, certifying the asserted strict signs
   at the roots of `A_n` on that finite range. Actual output:
   `common_a_interlacer.out`.
3. `identity_and_sign_check.py`: independently checked the defining finite-
   difference numerator of (1) and polynomial identity (6) for every
   `0<=n<=12`, all indices. It then checked the direct basis common-
   interlacer signs and multiplicity-aware real-root counts for `2<=n<=12`.
   Totals: 91 refined generating identities, 91 basis identities, and
   88 combined sign/root-count checks, all passed. Actual output:
   `identity_and_sign_check.out`.

These checks are corroboration; the all-degree argument is (1)–(11) and the
root count above.

## Source

Christos A. Athanasiadis, *On the real-rootedness of the Eulerian
transformation*, arXiv:2302.00754v5 (18 February 2025):
https://arxiv.org/html/2302.00754v5 .
The only substantive external dependency used here is the standard refined-
Eulerian interlacing family, explicitly stated there in Lemma 2.2(b) and
Example 2.3. The supplied packet's three-term theorem and its type A audit
are not used.
