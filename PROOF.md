# Proof

This is a readable account of the argument formalized in this repository. Each section names
the Lean file where the corresponding step is proved.

## Statement

Let $B_0=1$ and $B_{n+1}=(1+(2n+1)x)B_n+2x(1-x)B_n'$, and let $\mathcal B$ be the linear map
on real polynomials with $\mathcal B(t^m)=B_m(x)$. For $0\le k\le n$ put

```math
b(n,k)=\mathcal B\bigl(t^{n-k}(1+t)^k\bigr)=\sum_{j=0}^{k}\binom{k}{j}B_{n-j}(x).
```

**Theorem.** For every $n\ge1$ and every nonzero vector $c_0,\dots,c_n\ge0$, the polynomial
$F=\sum_k c_k\,b(n,k)$ has degree $n$ and $n$ real roots counted with multiplicity, all
strictly negative. For $n=0$, $F=c_0$.

The identity for $b(n,k)$ follows by expanding $(1+t)^k$ with the binomial theorem and
reindexing $j\mapsto k-j$ ([Basic.lean](TypeBEulerian/Basic.lean), `mathcalB_basis`). The
polynomials $B_n$ are RealRooted's `typeBEulerian`; `B_succ` restates its defining
recurrence in exactly the form above.

## 1. Euler numerators and the type B generating function

For a real polynomial $q$ of degree $n$, the power series $\sum_{m\ge0}q(m)x^m$ equals
$E[q]/(1-x)^{n+1}$ for a unique polynomial $E[q]$ of degree at most $n$, the *Euler
numerator* of $q$. RealRooted defines it as `polynomialValueEulerNumerator` and proves this
generating-series identity; [EulerNumerator.lean](TypeBEulerian/EulerNumerator.lean)
(`eulerNumerator_coe_eq`) restates it as
$E[q]=(1-x)^{n+1}\sum_m q(m)x^m$.

The type B Eulerian polynomials satisfy

```math
B_l(x)=(1-x)^{l+1}\sum_{m\ge0}(2m+1)^l x^m
```

(`B_coe_eq`).

Proof by induction on $l$. For $l=0$ this is the geometric series. Writing
$G_l=\sum_m(2m+1)^lx^m$, the coefficientwise identity $G_{l+1}=G_l+2xG_l'$ and the recurrence
for $B_{l+1}$ reduce the step to
$(1+(2l+1)x)-2(l+1)x=1-x$. The identity is one of formal power series, so no convergence
question arises.

## 2. A pointwise identity

Fix $0\le k\le n$ and a real $s\ne1$, and put

```math
q_s(t)=(2t+1)^{n-k}\bigl((1-s)(2t+1)+1\bigr)^k
      =\sum_{j=0}^{k}\binom{k}{j}(1-s)^{k-j}(2t+1)^{n-j}.
```

It has degree exactly $n$. By §1 applied to each $(2t+1)^{n-j}$,

```math
E[q_s](x)=\sum_{j=0}^{k}\binom{k}{j}(1-s)^{k-j}(1-x)^{j}B_{n-j}(x)
```

(`eulerNumerator_shiftedInput`), and evaluating at $x=s$ gives

```math
E[q_s](s)=(1-s)^k\,b(n,k)(s)
```

(`eval_eulerNumerator_shiftedInput`).

Since $B_{n-j}$ is monic of degree $n-j$ and $(1-x)^j$ has leading coefficient $(-1)^j$, the
coefficient of $x^n$ in $E[q_s]$ is
$\sum_j\binom kj(1-s)^{k-j}(-1)^j=(-s)^k$ (`coeff_eulerNumerator_shiftedInput`). For $s<0$ it
is positive, so $E[q_s]$ has degree $n$ and positive leading coefficient.

The real number $s$ is a fixed parameter of the input $q_s$. Only after $E[q_s]$ has been
formed as a polynomial in $x$ is it evaluated at the point $x=s$.

## 3. The ordinary Eulerian polynomial is a common interlacer

[CommonInterlacer.lean](TypeBEulerian/CommonInterlacer.lean).

Let $A_n$ be the ordinary Eulerian polynomial ($A_1=1$, $A_2=1+x$,
$A_{m+1}=(1+mx)A_m+x(1-x)A_m'$), RealRooted's `generalizedEulerian 1 (n-1)`.

- **Euler numerator.** $A_n=E[(t+1)^n]$ (`eulerNumerator_X_add_one_pow`), by the same
  power-series argument as §1 with $\sum_m(m+1)^nx^m$.
- **Simple negative roots.** $A_n$ has nonnegative coefficients and $A_n(0)=1$, so every root
  is negative. At a root $r$ of $A_m$, the recurrence gives
  $A_{m+1}(r)A_m'(r)=r(1-r)A_m'(r)^2<0$ when the roots of $A_m$ are simple. RealRooted's
  critical-sign lemma then gives that $A_m$ interlaces $A_{m+1}$ and that the roots of
  $A_{m+1}$ are simple. Induction on $m$ proves simplicity for all $n$
  (`generalizedEulerian_one_hasSimpleRoots`, `generalizedEulerian_one_root_neg`).
- **Brändén's theorem.** P. Brändén, *On linear transformations preserving the Pólya
  frequency property*, Trans. Amer. Math. Soc. 358 (2006), Theorem 4.6, formalized in
  RealRooted as `polynomialValueEulerNumerator_strictInterl_of_rootwiseLE`: if $f$ and $g$
  are monic of degree $n\ge1$, real-rooted with all roots in $[-1,0]$, and the sorted roots of
  $f$ are coordinatewise at most those of $g$, then $E[f]$ interlaces $E[g]$.

For $s\le0$, the polynomial $q_s$ is $2^{n-k}(2(1-s))^k$ times the monic polynomial
$(t+\tfrac12)^{n-k}(t+a)^k$ with $a=(2-s)/(2(1-s))\in[\tfrac12,1]$. Its roots lie in
$[-1,-\tfrac12]$, and every root of $(t+1)^n$ equals $-1$, so Brändén's theorem applies to
$f=(t+1)^n$. Scaling by the positive constant shows that **$A_n$ interlaces $E[q_s]$ for every
$s\le0$** (`strictInterl_eulerianA_eulerNumerator_shiftedInput`).

Here "interlaces" is RealRooted's `StrictInterl`: both polynomials are nonzero and
real-rooted, and their sorted roots alternate weakly, with shared roots allowed.

**Signs at the roots of $A_n$.** Let $r$ be a root of $A_n$, so $r<0$. By §2,
$E[q_r]$ has positive leading coefficient, and $A_n$ is monic. For positive-leading
polynomials with $A_n$ interlacing $E[q_r]$, RealRooted's
`StrictInterl.eval_mul_derivative_nonpos_of_left_root` gives
$\bigl(E[q_r]\bigr)(r)\,A_n'(r)\le0$. Dividing by $(1-r)^k>0$ and using §2:

```math
b(n,k)(r)\,A_n'(r)\le 0\qquad(0\le k\le n)
```

(`b_eval_mul_derivative_nonpos`).

## 4. The cone

[MainTheorem.lean](TypeBEulerian/MainTheorem.lean).

Let $c\ne0$ with $c_k\ge0$ and $F=\sum_kc_k\,b(n,k)$.

- Each $b(n,k)$ has degree at most $n$, coefficient $1$ at $x^n$, nonnegative coefficients,
  and $b(n,k)(0)=2^k$. So $F$ has degree exactly $n$, leading coefficient
  $\sum_kc_k>0$, nonnegative coefficients and $F(0)=\sum_kc_k2^k>0$.
- At every root $r$ of $A_n$, $F(r)A_n'(r)=\sum_kc_k\,b(n,k)(r)A_n'(r)\le0$ by §3.
- RealRooted's `strictInterl_of_eval_mul_derivative_nonpos`: if $f$ is real-rooted with
  simple roots and positive leading coefficient, $F$ has positive leading coefficient and
  degree $\deg f$ or $\deg f+1$, and $F(r)f'(r)\le0$ at every root $r$ of $f$, then $f$
  interlaces $F$. In particular $F$ is real-rooted. Apply it with $f=A_n$, of degree $n-1$.
  For $n=1$, $A_1=1$ has no roots and the conclusion is immediate.
- A real-rooted polynomial of degree $n$ has $n$ real roots with multiplicity. Nonnegative
  coefficients make every root nonpositive, and $F(0)>0$ excludes $0$.

For $n=0$, $F=c_0\,b(0,0)=c_0$, a nonzero constant, which is real-rooted under Mathlib's
convention. For $c=0$, $F=0$, which Mathlib's `Splits` also counts as real-rooted; the
repository states this case separately (`mathcalB_coneInput_zero`).

## Relation to the informal proof

The informal proof in [original/](original/README.md) gives two arguments. Its
operator (Cayley-transform) argument proves the stronger facts that every nonzero cone image
has simple roots and that $(b(n,n),\dots,b(n,0))$ is an interlacing sequence. Its
refined-Eulerian argument writes $(1-x)^kb(n,k)$ as a combination
$\sum_jW_{n,k,j}(x)\,p_{n,j}(x)$ of the refined Eulerian polynomials, with weights positive at
negative $x$, and uses the interlacing of the refined family.

The Lean proof follows the refined route but evaluates pointwise: at $x=r$ the weighted
combination is exactly $E[q_r]$, and Brändén's Theorem 4.6 supplies the needed sign without
formalizing the refined family. It proves weak signs only, which suffice for
real-rootedness. Simplicity of the roots and the strict interlacing of the basis images are
**not** formalized here.
