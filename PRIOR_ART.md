# Prior art

## Origin and statement

C. A. Athanasiadis, *On the real-rootedness of the Eulerian transformation*,
[arXiv:2302.00754v5](https://arxiv.org/abs/2302.00754v5) (February 18, 2025), published in
J. London Math. Soc., DOI [10.1112/jlms.70083](https://doi.org/10.1112/jlms.70083), is the
source of the statement. Its Remark 7.2(b) defines type B analogues
$\mathcal B,\mathcal D^B:\mathbb R_n[x]\to\mathbb R_n[x]$ of the Eulerian and derangement
transformations by $\mathcal B(x^n)=B_n(x)$, the standard type B Eulerian polynomial (citing
Petersen, *Eulerian Numbers*, §11.4), and
$\mathcal D^B(x^n)=\sum_{i=0}^{n}(-1)^i\binom ni B_{n-i}(x)$. It states that computational
evidence suggests $\mathcal B(p)$ and $\mathcal D^B(p)$ have only real roots for every
$p\in\mathcal P_n$, the nonnegative combinations of $x^{n-k}(1+x)^k$.

The remark is a report of computational evidence, not a numbered conjecture. This review
checked the remark's wording and the definition of $\mathcal P_n$ against the arXiv HTML
version (v5) on November 15, 2026. The paper does not restate the recurrence for $B_n$; the
recurrence used here is the standard one and gives $B_1=1+x$ and $B_2=1+6x+x^2$.

Remark 7.2(c) asks, more generally, for conditions on a sequence $h_n$ under which the rows
$h_{n,k}=\sum_i\binom ki x^ih_{n-i}$ and $\ell_{n,k}=\sum_i(-1)^i\binom kih_{n-i}$ are
interlacing sequences of real-rooted polynomials.

## Closest related work and unresolved overlap

- **Liu and Yan (2025).** L. L. Liu and X. Yan, *Some interlacing properties related to the
  Eulerian and derangement polynomials*, Adv. in Appl. Math. **162** (2025) 102776,
  DOI [10.1016/j.aam.2024.102776](https://doi.org/10.1016/j.aam.2024.102776), §3, studies
  "positive rows" of binomial sums of a polynomial sequence. Since $B_n$ is palindromic,
  ```math
  x^n\,b(n,k)(1/x)=\sum_{i=0}^{k}\binom ki x^iB_{n-i}(x),
  ```
  which is their positive row for the starting sequence $f_n=B_n$. The publisher's preview
  shows their recurrence (3.1), which the type B Eulerian polynomials satisfy with
  $(a_1,a_2,b_1,b_2,c_1,a_3,b_3)=(0,1,2,-1,0,2,-2)$, but it does not show all of the
  positive-row hypotheses. **Whether their §3 theorem applies to $f_n=B_n$, and so already
  implies the statement proved here, is unresolved.** A fixed-row interlacing theorem that
  applies would imply real-rootedness on the cone. This repository makes no claim either
  way.
- **Yan and Liu (2025).** X. Yan and L. L. Liu, *Some interlacing sequences related to the
  Eulerian and derangement polynomials*, Discrete Math. **348**(11) (2025) 114598,
  DOI [10.1016/j.disc.2025.114598](https://doi.org/10.1016/j.disc.2025.114598). Its
  introduction states the full nonnegative-cone result for the **derangement** map
  $\mathcal D^B$, with an interlacing refinement, and credits Liu and Yan. That result is
  already in the literature and is not claimed here. It is not, by itself, evidence for the
  map $\mathcal B$: shifting the input by $t\mapsto t+1$ does not preserve the cone
  $\mathcal P_n$.
- **Brändén and Vecchi (2025).** P. Brändén and L. Vecchi, *Chow polynomials of totally
  nonnegative matrices and posets*, [arXiv:2509.17852v3](https://arxiv.org/abs/2509.17852),
  §4.3, proves real-rootedness for Chow–Eulerian transformations. Its theorem statements do
  not identify those maps and input bases with $\mathcal B$ on $\mathcal P_n$, and no such
  identification is assumed here.

## Proof ingredients used

- **Brändén's Theorem 4.6.** P. Brändén, *On linear transformations preserving the Pólya
  frequency property*, Trans. Amer. Math. Soc. **358** (2006),
  [arXiv:math/0403364](https://arxiv.org/abs/math/0403364). The Lean proof uses the
  RealRooted formalization of this theorem.
- **Refined Eulerian polynomials.** The informal refined-family proof uses the standard
  refined Eulerian family and its interlacing, as stated in Athanasiadis (Lemma 2.2(b) and
  Example 2.3). The Lean proof does not use them.
- **Related fixed-parameter and endpoint facts.** D. Karp and A. Vishnyakova,
  [arXiv:2509.13897](https://arxiv.org/abs/2509.13897), §2, and S. Janson's note on
  Euler–Frobenius polynomials, [arXiv:1305.3512](https://arxiv.org/abs/1305.3512), p. 3,
  contain fixed-parameter real-rootedness and endpoint identities related to the informal
  operator argument. Neither is used by the Lean proof, and neither is identified here as
  covering the statement.
- **Library.** The [RealRooted](https://github.com/PerAlexandersson/RealRooted) Lean library
  at commit `d667074` supplies the type B Eulerian polynomials, Euler numerators, Brändén's
  theorem and the interlacing criteria. At that commit it does not contain this statement.

## Novelty statement

A bounded AI-assisted search (November 14–15, 2026) checked the source paper, exact titles
and phrases for type B Eulerian and derangement transformations, and the 2025 follow-ups
above. It did **not** locate a published proof of the exact statement for $\mathcal B$. The
Liu–Yan overlap above remains unresolved because their full hypotheses were not accessible.
This is a finding about the sources checked, **not a claim of novelty, first discovery or
historical priority**. The purpose of this repository is to provide a checkable proof for
researchers investigating this statement.

What was already known or is not claimed here:

- the statement itself, reported by Athanasiadis as supported by computational evidence;
- the cone result for $\mathcal D^B$ (Liu–Yan, as stated by Yan–Liu);
- the methods: Euler numerators, Brändén's theorem, common interlacers and sign criteria.

**Results provided in this repository:** a Lean-checked proof that $\mathcal B(p)$ has only
real roots for every nonzero $p\in\mathcal P_n$, with degree $n$ and negative roots, and an
informal proof (not formalized) of simple roots, of the interlacing of the basis images, and
of the larger-cone and $\mathcal D^B$ statements.

## Access limitations

- The full texts of Liu–Yan (2025) and Yan–Liu (2025) were not accessed; publisher pages
  returned errors, and only abstracts, previews and indexed introductions were read.
- Petersen's *Eulerian Numbers* was not consulted; the standard type B normalization was
  checked against the recurrence and the small cases $B_1$, $B_2$.
- Brändén–Vecchi was checked at its transformation theorems only.
