# Real-Rootedness of the Type B Eulerian Transformation on the Cone $\mathcal P_n$

**By Chris Ozols, with AI-assisted proof development and formalization.**

> **Lean-checked proof; no novelty claim.** The statement proved here is the Eulerian-map
> part of Athanasiadis's Remark 7.2(b), which the paper reports as supported by
> computational evidence. A bounded search did not locate a published proof of this exact
> statement, but closely related work by Liu and Yan (2025) may already imply it; that
> overlap is **unresolved**. I do not claim novelty, first discovery, or priority. This
> repository makes the argument and its Lean checks available to anyone investigating it.
> See the [prior-art review](PRIOR_ART.md).

Let $B_n(x)$ be the type B Eulerian polynomials, $B_0=1$ and

```math
B_{n+1}(x)=\bigl(1+(2n+1)x\bigr)B_n(x)+2x(1-x)B_n'(x),
```

so $B_1=1+x$ and $B_2=1+6x+x^2$. Let $\mathcal B:\mathbb R[t]\to\mathbb R[x]$ be the linear
map with $\mathcal B(t^m)=B_m(x)$. This repository proves, in **Lean 4.35.0 with Mathlib
v4.35.0 and the RealRooted library**, that for every $n\ge 0$ and all real
$c_0,\dots,c_n\ge 0$, not all zero, the polynomial

```math
\mathcal B\Bigl(\sum_{k=0}^{n} c_k\,t^{\,n-k}(1+t)^k\Bigr)
```

has only real roots. In fact the image has degree exactly $n$ and $n$ real roots counted with multiplicity, all
strictly negative. The all-zero vector gives the zero polynomial; $n=0$ gives the constant
$c_0$.

> **Trust model.** Every audited theorem depends only on Lean's standard axioms
> `propext`, `Classical.choice` and `Quot.sound`. There is no `native_decide`, no
> `sorry`, and no project-specific axiom, so the proofs are checked by the Lean kernel,
> including every RealRooted and Mathlib lemma they use. See [Trust model](#trust-model).

[Readable proof](PROOF.md) · [Main Lean theorem](TypeBEulerian/MainTheorem.lean) ·
[Exact-statement check](Verification.lean) ·
[Verification report](VERIFICATION_REPORT.md) · [Provenance](PROVENANCE.md) ·
[Prior art](PRIOR_ART.md) · [Citation](CITATION.cff)

## The question and what is proved

C. A. Athanasiadis, *On the real-rootedness of the Eulerian transformation*
([arXiv:2302.00754v5](https://arxiv.org/abs/2302.00754v5), J. London Math. Soc.,
DOI [10.1112/jlms.70083](https://doi.org/10.1112/jlms.70083)), Remark 7.2(b), defines type B
analogues $\mathcal B$ and $\mathcal D^B$ of the Eulerian and derangement transformations and
reports that computational evidence suggests $\mathcal B(p)$ and $\mathcal D^B(p)$ have only
real roots for every $p\in\mathcal P_n$. Here $\mathcal P_n$ is the set of nonnegative linear
combinations of $t^{n-k}(1+t)^k$, $0\le k\le n$. This repository treats **only the Eulerian
map $\mathcal B$**.

The basis images are

```math
b(n,k)=\mathcal B\bigl(t^{n-k}(1+t)^k\bigr)=\sum_{j=0}^{k}\binom{k}{j}B_{n-j}(x).
```

| Statement | Status | Lean declaration |
| --- | --- | --- |
| $\mathcal B(p)$ has only real roots for every nonzero $p\in\mathcal P_n$ | Formalized | `TypeBEulerian.mathcalB_coneInput_splits` |
| … and is nonzero, of degree $n$, with $n$ real roots (with multiplicity), all negative | Formalized | `TypeBEulerian.mathcalB_coneInput_realRooted` |
| All-zero coefficients; the case $n=0$ | Formalized | `mathcalB_coneInput_zero`, `mathcalB_coneInput_n_zero` |
| The basis-image formula for $b(n,k)$ | Formalized | `TypeBEulerian.mathcalB_basis` |
| $b(n,k)(r)\,A_n'(r)\le 0$ at every root $r$ of the Eulerian polynomial $A_n$ | Formalized | `TypeBEulerian.b_eval_mul_derivative_nonpos` |
| Roots of every nonzero $\mathcal B(p)$ are **simple**; $(b(n,n),\dots,b(n,0))$ is an interlacing sequence | Informal proof only ([original/](original/README.md)) | — |
| The derangement map $\mathcal D^B$; the larger cone spanned by $(t-1)^{n-j}(t+1)^j$ | Informal proof only; $\mathcal D^B$ already in the literature | — |

"Only real roots" is Mathlib's `Polynomial.Splits` over $\mathbb R$: the polynomial is a
product of a constant and monic linear factors. The strong form also states
`roots.card = n = natDegree`. [Verification.lean](Verification.lean) restates the results
for **any** sequence satisfying the recurrence above and **any** linear map sending $t^m$ to
its $m$-th term, using only Mathlib notions, and proves that such a sequence and map exist,
so its hypotheses are not vacuous.

## Proof overview

1. **Euler numerators.** For a polynomial $q$ of degree $n$, let $E[q]$ be the polynomial
   with $\sum_{m\ge0}q(m)x^m=E[q]/(1-x)^{n+1}$. The type B generating function
   $\sum_m(2m+1)^lx^m=B_l/(1-x)^{l+1}$ is proved from the recurrence.
2. **A pointwise identity.** For a real $s<1$ put
   $q_s(t)=(2t+1)^{n-k}\bigl((1-s)(2t+1)+1\bigr)^k$. Then
   $\bigl(E[q_s]\bigr)(s)=(1-s)^k\,b(n,k)(s)$.
3. **A common interlacer.** The ordinary Eulerian polynomial $A_n=E[(t+1)^n]$ has simple
   negative roots. For $s\le0$, $q_s$ is a positive multiple of a monic polynomial whose
   roots lie in $[-1,-\tfrac12]$, so Brändén's Theorem 4.6 (as formalized in RealRooted)
   makes $A_n$ interlace $E[q_s]$. Taking $s=r$, a root of $A_n$, gives
   $b(n,k)(r)\,A_n'(r)\le0$.
4. **The cone.** These signs survive nonnegative combinations. A sign criterion in
   RealRooted then shows that $A_n$ interlaces every nonzero
   $\sum_kc_k\,b(n,k)$, which therefore has only real roots. Nonnegative coefficients and a
   positive constant term make every root negative.

[PROOF.md](PROOF.md) gives the full argument and the Lean file for each step.

## Trust model

`./verify.sh` prints the type and the axioms of 12 declarations: the project's main
theorems and the restatements in [Verification.lean](Verification.lean). Each must depend on
exactly `propext`, `Classical.choice` and `Quot.sound`. Lean's `#print axioms` reports the
full transitive closure, so this covers every RealRooted and Mathlib lemma used; any
`sorryAx`, `Lean.ofReduceBool` or added axiom would fail the audit.
[scripts/audit.py](scripts/audit.py) also rejects `sorry`, `admit`, axiom declarations,
`native_decide`, `unsafe`, `implemented_by`, `extern`, attributes, instances, notation and
macros in this project's Lean files.

The proof depends on the **statements** of RealRooted's theorems being correct Lean
theorems, which the kernel checks during the build. It does not depend on any informal claim
in RealRooted's documentation. The Lean definitions this project relies on are RealRooted's
`typeBEulerian` (restated as the recurrence above in `B_succ`) and its
`polynomialValueEulerNumerator`, which enters only inside the proof.

## Reproduce the verification

On Linux x86_64 with Bash, Git, Python 3, curl, tar, zstd and coreutils:

```sh
git clone https://github.com/cozuya/eulerian-transformation-type-b.git
cd eulerian-transformation-type-b
bash scripts/install-lean.sh
export PATH="$PWD/.tools/lean-4.35.0-linux/bin:$PATH"
bash scripts/fetch-deps.sh        # locked RealRooted + Mathlib, prebuilt Mathlib
./verify.sh                       # rebuild + statement/axiom audit
python3 scripts/check-package.py
```

RealRooted has no prebuilt cache, so the first build compiles the RealRooted modules this
project imports from source. See [REPRODUCE.md](REPRODUCE.md) for details, timings and
resource needs.

| Component | Pinned version or revision |
| --- | --- |
| Lean | 4.35.0, `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Lake | `5.0.0-src+eb6cafb` |
| Mathlib | v4.35.0, `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| RealRooted | `d667074269bb822fa18ca9142a14fdd90734dd57` |

The committed [local evidence](evidence/verification.json) identifies its sources by hash.

## Provenance

Chris Ozols directed the work. The informal proof ([original/](original/README.md)) was
developed with AI assistants. The Lean formalization and this package were written by
Anthropic's Claude, building on the [RealRooted](https://github.com/PerAlexandersson/RealRooted)
library, which supplies the type B Eulerian polynomials, Euler numerators, Brändén's
Theorem 4.6 and the interlacing criteria. [PROVENANCE.md](PROVENANCE.md) gives dates,
sources and what each record does and does not establish.

Formal verification establishes the stated results relative to Lean and its kernel. It does
not establish historical priority. [PRIOR_ART.md](PRIOR_ART.md) records the literature review
and its access limitations.

## Discovery and novelty-checking summary

**Search identifiers:** type B Eulerian transformation; Athanasiadis Remark 7.2(b);
real-rootedness of the Eulerian transformation; type B Eulerian polynomials; signed
permutations descent polynomial; $\mathcal B(t^n)=B_n$; nonnegative combinations of
$t^{n-k}(1+t)^k$; Lean RealRooted.

**Exact scope:** real-rootedness of $\mathcal B(p)$ for every nonzero $p\in\mathcal P_n$,
every $n$, with degree $n$ and negative roots. Simple roots, the interlacing of the basis
images, the larger cone and $\mathcal D^B$ are not formalized. The
[Lean statements](Verification.lean), [verification report](VERIFICATION_REPORT.md) and
[prior-art review](PRIOR_ART.md) enable a direct novelty check.

## License

Copyright 2026 Chris Ozols. The Lean proofs, scripts, and documentation in this
repository are licensed under the [Apache License, Version 2.0](LICENSE).
Third-party dependencies, including RealRooted and Mathlib, retain their respective
licenses. The preserved informal proof material in [original/](original/README.md) is
included under the same license.
