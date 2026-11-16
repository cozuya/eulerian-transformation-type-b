# Verification and statement correspondence

The reproducible entry point is `./verify.sh`. Its complete output is retained in
[evidence/verification.log](evidence/verification.log), with machine-readable metadata in
[evidence/verification.json](evidence/verification.json) and the exact theorem types and
axiom reports in [evidence/kernel-check.log](evidence/kernel-check.log).

## What the theorems say

The main theorem, in [TypeBEulerian/MainTheorem.lean](TypeBEulerian/MainTheorem.lean), as
printed by Lean:

```text
TypeBEulerian.mathcalB_coneInput_splits : ∀ (n : ℕ) (c : Fin (n + 1) → ℝ),
  (∀ (k : Fin (n + 1)), 0 ≤ c k) → c ≠ 0 →
    (TypeBEulerian.mathcalB (∑ k, c k • (X ^ (n - ↑k) * (1 + X) ^ ↑k))).Splits
```

The names it uses:

- `TypeBEulerian.B n` is RealRooted's `typeBEulerian n`. The project proves `B 0 = 1` and
  `B (n + 1) = (1 + C (2n+1) * X) * B n + C 2 * X * (1 - X) * derivative (B n)`
  (`B_succ`), together with `B 1 = 1 + X` and `B 2 = 1 + 6 * X + X ^ 2`.
- `TypeBEulerian.mathcalB : ℝ[X] →ₗ[ℝ] ℝ[X]` is the real-linear map with
  `mathcalB (X ^ m) = B m` (`mathcalB_X_pow`), defined by `Polynomial.lsum`.
- `Polynomial.Splits` is Mathlib's: the polynomial is a product of a constant and monic linear
  factors over `ℝ`. For a nonzero polynomial this is equivalent to
  `p.roots.card = p.natDegree` (Mathlib's `splits_iff_card_roots`).
- The input variable `t` of the informal statement is Mathlib's `X` on the input side.

The project defines no replacement for any Mathlib notion, and the source audit rejects
notation, macros, instances and attribute changes that could alter them.

[Verification.lean](Verification.lean) imports the proof and restates the results without the
project's definitions. It assumes a sequence `P : ℕ → ℝ[X]` with
`P 0 = 1 ∧ ∀ n, P (n+1) = (1 + C (2n+1) * X) * P n + C 2 * X * (1 - X) * derivative (P n)`
(`IsTypeBEulerian P`) and any `L : ℝ[X] →ₗ[ℝ] ℝ[X]` with `∀ m, L (X ^ m) = P m`, and proves:

| Declaration | Statement |
| --- | --- |
| `TypeBEulerianVerification.real_rooted` | for every `n` and `c : Fin (n+1) → ℝ` with `c ≥ 0`, `c ≠ 0`: `L (∑ k, c k • (X^(n-k) * (1+X)^k))` splits |
| `TypeBEulerianVerification.real_rooted_strong` | that polynomial is nonzero, splits, has `natDegree = n` and `roots.card = n`, and every root is `< 0` |
| `TypeBEulerianVerification.zero_vector` | the all-zero coefficient vector gives `0` |
| `TypeBEulerianVerification.degree_zero` | for `n = 0` the image is `C (c 0)` |
| `TypeBEulerianVerification.basis_image` | `L (X^(n-k) * (1+X)^k) = ∑_{j ≤ k} (k choose j) • P (n-j)` for `k ≤ n` |
| `TypeBEulerianVerification.sequence_exists` | some `P` satisfies `IsTypeBEulerian`, with `P 1 = 1 + X` and `P 2 = 1 + 6X + X²` |
| `TypeBEulerianVerification.map_exists` | for such `P`, some linear `L` has `L (X ^ m) = P m` |

The last two show that the hypotheses are satisfiable, so the other statements are not
vacuous. There are no other hypotheses: `n` is arbitrary, and boundary coefficient vectors
(with zeros) are included.

## Trust model

`./verify.sh` audits the printed axioms of 12 declarations: the 7 restatements above and 5
project theorems (`mathcalB_coneInput_splits`, `mathcalB_coneInput_realRooted`,
`mathcalB_coneInput_zero`, `mathcalB_coneInput_n_zero`, `b_eval_mul_derivative_nonpos`).

| Axioms | Declarations |
| --- | --- |
| `propext`, `Classical.choice`, `Quot.sound` only | all 12 |

`#print axioms` reports the transitive closure, including every RealRooted and Mathlib lemma
used, so the audit would detect `sorryAx`, `native_decide` (`Lean.ofReduceBool`,
`Lean.trustCompiler`) or any added axiom anywhere in the dependency chain. The theorems are
therefore checked by the Lean kernel alone, without trusting the Lean compiler.

The source scan rejects `sorry`, `admit`, `axiom` declarations, `native_decide`, `unsafe`,
`implemented_by`, `extern`, `csimp`, `opaque`, kernel-checking options, attributes,
instances, notation and macros in this project's six Lean files. It does not scan
RealRooted's sources; the axiom audit covers what the theorems actually use.

## Measured results

The recorded local run took place from 2026-11-16 00:06:32 to 00:10:49 UTC (4 min 17 s). The
machine was a WSL2 Linux host with 24 hardware threads. RealRooted's build outputs were
deleted first, so the build compiled the RealRooted modules from source; Mathlib came from
its prebuilt cache.

| Step | Result |
| --- | --- |
| Pins, source scan, inventory, 44 source hashes | PASS |
| `rm -rf .lake/build`, then `lake build TypeBEulerian` | 9,410 jobs, exit 0, 253 s wall time; 357 RealRooted modules and the 5 project modules compiled from source |
| `lake env lean --trust=0 Verification.lean` | exit 0, no warnings or errors, 4 s |
| Axiom audit | all 12 declarations exactly as expected |
| Whole script | exit 0; 4 min 17 s wall time; 1,703 s user CPU; largest single-process resident size 7.4 GB |

The same sources were also built and audited in the private development repository, and
again from a fresh clone of it, before this package was assembled. Those runs used the same
pins and gave the same axiom reports.

## Commands

After installing the pinned compiler and fetching the locked dependencies, as described in
[REPRODUCE.md](REPRODUCE.md):

```sh
./verify.sh
python3 scripts/check-package.py
```

## Limits of what is verified

- Only the statements above are formalized. Simple roots of the cone images, the strict
  interlacing of $b(n,n),\dots,b(n,0)$, the larger cone and the derangement map
  $\mathcal D^B$ are proved only informally ([original/](original/README.md)).
- The theorems are about RealRooted's definitions as restated above. The correspondence with
  the paper's $B_n$ rests on the recurrence and the standard normalization; the paper itself
  defines $B_n$ by citation.
- The Lean proof uses RealRooted's formalization of Brändén's Theorem 4.6 and its
  interlacing criteria. Their correctness as Lean theorems is checked by the kernel; whether
  they match the cited literature is not needed for the result.
- Verification establishes the stated theorems. It does not establish historical priority;
  see [PRIOR_ART.md](PRIOR_ART.md).
