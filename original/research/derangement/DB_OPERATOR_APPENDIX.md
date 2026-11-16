# Operator extension: strong row interlacing for the type B derangement map

This appendix uses Sections 1–4 of `research/operator/PROOF.md`. It contains no new external mathematical dependency.

## Setup already established in that proof

Let

\[
T=2(z^2-1)\frac{d}{dz}+2z,\qquad C_n=T^n1,
\]

and let \(r_1<\cdots<r_n\) be the simple roots of \(C_n\) in \((-1,1)\). The proof establishes endpoint polynomials

\[
(T+2)^n1=(z+1)R_{n-1}(z),\qquad
(T-2)^n1=(z-1)R_{n-1}(z).
\]

Writing the roots of the first as \(u_1=-1<u_2<\cdots<u_n\), one has

\[
u_i<r_i<u_{i+1}\quad(i<n),\qquad u_n<r_n<1.
\tag{A1}
\]

The ordered roots of \(\prod_{j=1}^n(T+c_j)1\) strictly decrease as any constant parameter \(c_j\in(-2,2)\) increases.

## 1. Constant parameters for the secondary family

For \(0\le k\le n\) and a real constant \(-2<a<0\), set

\[
G_{n,k}(z;a)=T^k(T+a)^{n-k}1.
\]

If \(k<n\), all its roots \(\lambda_{i,k}(a)\) are simple and satisfy

\[
r_i<\lambda_{i,k}(a)<u_{i+1}\quad(i<n),\qquad
r_n<\lambda_{n,k}(a)<1.
\tag{A2}
\]

This follows by comparing its constant parameter vector with the all-zero and all-minus-two vectors. Strictness is obtained by a small change of an interior parameter before taking the endpoint limit. For \(k=n\), \(G_{n,n}=C_n\).

At a fixed \(a\in(-2,0)\), increasing \(k\) replaces one negative parameter by zero. Therefore

\[
\lambda_{i,k+1}(a)<\lambda_{i,k}(a)\qquad(k<n).
\tag{A3}
\]

## 2. The variable substitution and root count

Let

\[
d_{n,k}(x)=\mathcal D^B(t^{n-k}(1+t)^k)(x).
\]

Using \(\mathcal D^B(p(t))=\mathcal B(p(t-1))\) gives

\[
\delta_{n,k}(z):=(z+1)^n d_{n,k}\!\left(\frac{z-1}{z+1}\right)
=\left.G_{n,k}(z;a)\right|_{a=-(z+1)}.
\tag{A4}
\]

The right side means expansion with constant \(a\), followed by substitution. It does not mean composition of variable-coefficient operators \(T-(z+1)\).

For \(k<n\) and \(i<n\), define the continuous function

\[
H_{i,k}(z)=z-\lambda_{i,k}(-z-1).
\]

Equation (A2) gives

\[
H_{i,k}(r_i)<0,\qquad H_{i,k}(u_{i+1})>0.
\tag{A5}
\]

Thus \(\delta_{n,k}\) has a root in every one of the \(n-1\) disjoint intervals \((r_i,u_{i+1})\). Also,

\[
\delta_{n,k}(1)=G_{n,k}(1;-2)=2^k(2-2)^{n-k}=0.
\tag{A6}
\]

The polynomial in (A4) has degree at most \(n\), and it is nonzero because
\(\delta_{n,k}(-1)=C_n(-1)=(-2)^n\). Equations (A5)–(A6) supply \(n\) distinct roots, so its degree is exactly \(n\). Consequently it has exactly one simple root \(s_{i,k}\) in each interval \((r_i,u_{i+1})\), and its last root is \(s_{n,k}=1\).

This degree argument is essential. We do not assert that \(H_{i,k}\) has positive derivative. It has exactly one zero in its band, and its endpoint signs imply that it is negative before that zero and positive after it.

For \(k=n\), set \(s_{i,n}=r_i\).

## 3. Ordering the roots within each band

If \(k<\ell<n\), evaluate the constant-parameter root inequality (A3) at
\(a=-s_{i,k}-1\). It gives

\[
H_{i,\ell}(s_{i,k})
=s_{i,k}-\lambda_{i,\ell}(-s_{i,k}-1)>0.
\]

Since \(H_{i,\ell}\) has exactly one zero in the band and is negative before it and positive after it,

\[
s_{i,\ell}<s_{i,k}\qquad(i<n).
\tag{A7}
\]

This remains true for \(\ell=n\), because \(s_{i,n}=r_i\). For the last roots,
\(s_{n,k}=1\) for \(k<n\), while \(s_{n,n}=r_n<1\).

Adjacent bands are separated by

\[
s_{i,k}<u_{i+1}<r_{i+1}\le s_{i+1,\ell}\qquad(i<n),
\tag{A8}
\]

with the evident interpretation \(s_{n,\ell}=1\) or \(r_n\). Equations (A7)–(A8) prove that for \(k<\ell\),

\[
\delta_{n,\ell}\preceq\delta_{n,k}.
\]

The increasing Cayley map \(x=(z-1)/(z+1)\) maps \((-1,1]\) to \((-\infty,0]\). Therefore

\[
\boxed{(d_{n,n},d_{n,n-1},\ldots,d_{n,0})\text{ is an interlacing sequence}.}
\]

Every \(d_{n,k}\) has \(n\) distinct nonpositive roots. The endpoint \(d_{n,n}=B_n\) has no zero root; every other row member has a simple root at zero.

The case \(n=1\) also follows directly from \(d_{1,0}=x\), \(d_{1,1}=1+x\); \(n=0\) is constant.

## 4. Nonnegative combinations, without a compatibility theorem

For \(k<n\), the root locations above imply

\[
\operatorname{sgn}\delta_{n,k}(r_i)=(-1)^{n-i+1}\qquad(1\le i\le n),
\]

while \(\delta_{n,n}(r_i)=0\). To justify the positive leading sign directly, use \(\delta_{n,k}(-1)=(-2)^n\) and its \(n\) simple roots in \((-1,1]\).

Suppose at least one coefficient \(c_k>0\) with \(k<n\). The combination \(\sum_kc_k\delta_{n,k}\) has alternating nonzero signs at \(r_1,\ldots,r_n\), hence \(n-1\) distinct roots between them. Its value at \(z=1\) is \(2^nc_n\). If \(c_n>0\), it has one further root in \((r_n,1)\); if \(c_n=0\), its further root is \(z=1\). Degree at most \(n\) again proves that all these roots are simple and exhaustive. If only \(c_n>0\), the combination is a positive multiple of \(C_n\). This recovers the full secondary cone conclusion.
