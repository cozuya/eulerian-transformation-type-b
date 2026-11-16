import TypeBEulerian.CommonInterlacer
import RealRooted.MaWang.Weak.DerivativeSign

/-!
# Athanasiadis, Remark 7.2(b): the Eulerian map `ℬ`

For every `n` and every coefficient vector `c : Fin (n+1) → ℝ` with `c k ≥ 0`, put
`p(t) = ∑_{k=0}^{n} c_k t^(n-k) (1+t)^k` (`coneInput n c`).

* `mathcalB_coneInput_splits` (**main theorem**): if `c` is not identically zero, then
  `ℬ(p)` splits over `ℝ`, i.e. has only real roots. Moreover `ℬ(p)` is nonzero, has degree
  exactly `n`, has exactly `n` real roots counted with multiplicity, and all of them are
  strictly negative (`mathcalB_coneInput_realRooted`).
* `mathcalB_coneInput_zero`: the all-zero vector gives the zero polynomial (which splits,
  under Mathlib's convention).
* `mathcalB_coneInput_n_zero`: for `n = 0`, `ℬ(p)` is the constant `c 0`.

"Only real roots" is Mathlib's `Polynomial.Splits` for `ℝ[X]` (a product of a constant and
monic linear factors over `ℝ`); for a nonzero polynomial it is equivalent to
`p.roots.card = p.natDegree` (`Polynomial.splits_iff_card_roots`), which is also stated.
-/

open Polynomial

noncomputable section

namespace TypeBEulerian

open RealRooted

theorem natDegree_b_le {n k : ℕ} (hk : k ≤ n) : (b n k).natDegree ≤ n := by
  rw [b]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_smul_le _ _).trans ((RealRooted.natDegree_typeBEulerian _).le.trans (by omega))

theorem coeff_b_top {n k : ℕ} (hk : k ≤ n) : (b n k).coeff n = 1 := by
  rw [b, finsetSum_coeff, Finset.sum_eq_single 0]
  · simp [(RealRooted.coeff_typeBEulerian_top_and_above n).1]
  · intro j hj hj0
    have hj' : j ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hk
    rw [coeff_smul, (RealRooted.coeff_typeBEulerian_top_and_above (n - j)).2 n (by omega),
      smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h

theorem eval_zero_b (n k : ℕ) : (b n k).eval 0 = 2 ^ k := by
  rw [b, eval_finsetSum]
  simp only [eval_smul, smul_eq_mul]
  have h0 : ∀ m, (B m).eval 0 = 1 := fun m => by
    rw [← coeff_zero_eq_eval_zero]; exact RealRooted.coeff_typeBEulerian_zero m
  simp only [h0, mul_one]
  have := (add_pow (1 : ℝ) 1 k).symm
  simp only [one_pow, one_mul, one_add_one_eq_two] at this
  rw [← this]

theorem b_nonnegCoeffs (n k : ℕ) : HasNonnegCoeffs (b n k) := by
  intro m
  rw [b, finsetSum_coeff]
  exact Finset.sum_nonneg fun j _ => by
    rw [coeff_smul, smul_eq_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (RealRooted.typeBEulerian_nonnegCoeffs _ m)

/-- `ℬ` of the zero coefficient vector is `0`. -/
theorem mathcalB_coneInput_zero (n : ℕ) : mathcalB (coneInput n 0) = 0 := by
  simp [coneInput]

/-- For `n = 0`, `ℬ(c_0 · 1) = c_0`. -/
theorem mathcalB_coneInput_n_zero (c : Fin 1 → ℝ) : mathcalB (coneInput 0 c) = C (c 0) := by
  rw [mathcalB_coneInput, Fin.sum_univ_one, show ((0 : Fin 1) : ℕ) = 0 from rfl, b_zero_zero,
    smul_eq_C_mul, mul_one]

/-- Main theorem (strong form): for a nonnegative, not identically zero coefficient vector,
`ℬ(∑ c_k t^(n-k) (1+t)^k)` is a nonzero split polynomial of degree `n`, with `n` real roots
counted with multiplicity, all strictly negative. -/
theorem mathcalB_coneInput_realRooted (n : ℕ) (c : Fin (n + 1) → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hc0 : c ≠ 0) :
    mathcalB (coneInput n c) ≠ 0 ∧ (mathcalB (coneInput n c)).Splits ∧
      (mathcalB (coneInput n c)).natDegree = n ∧
      (mathcalB (coneInput n c)).roots.card = n ∧
      ∀ r ∈ (mathcalB (coneInput n c)).roots, r < 0 := by
  set F := mathcalB (coneInput n c) with hF
  rw [mathcalB_coneInput] at hF
  obtain ⟨k₀, hk₀⟩ : ∃ k, c k ≠ 0 := by
    by_contra h; push Not at h; exact hc0 (funext h)
  have hsum_pos : 0 < ∑ k : Fin (n + 1), c k :=
    Finset.sum_pos' (fun k _ => hc k) ⟨k₀, Finset.mem_univ _, (hc k₀).lt_of_ne' hk₀⟩
  have hdeg_le : F.natDegree ≤ n := by
    rw [hF]
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_smul_le _ _).trans (natDegree_b_le (Nat.lt_succ_iff.mp k.isLt))
  have hcoeff : F.coeff n = ∑ k : Fin (n + 1), c k := by
    rw [hF, finsetSum_coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_smul, coeff_b_top (Nat.lt_succ_iff.mp k.isLt), smul_eq_mul, mul_one]
  have hdeg : F.natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero hdeg_le (hcoeff ▸ hsum_pos.ne')
  have hF_pos : HasPosLeadingCoeff F := by
    rw [HasPosLeadingCoeff, leadingCoeff, hdeg, hcoeff]; exact hsum_pos
  have hF_ne : F ≠ 0 := hF_pos.ne_zero
  have hF_nonneg : HasNonnegCoeffs F := by
    intro m
    rw [hF, finsetSum_coeff]
    exact Finset.sum_nonneg fun k _ => by
      rw [coeff_smul, smul_eq_mul]; exact mul_nonneg (hc k) (b_nonnegCoeffs n k m)
  have hF0 : 0 < F.eval 0 := by
    rw [hF, eval_finsetSum]
    simp only [eval_smul, smul_eq_mul, eval_zero_b]
    exact Finset.sum_pos' (fun k _ => mul_nonneg (hc k) (by positivity))
      ⟨k₀, Finset.mem_univ _, mul_pos ((hc k₀).lt_of_ne' hk₀) (by positivity)⟩
  have hsplits : F.Splits := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
      exact Splits.C _
    · have hA_pos : HasPosLeadingCoeff (eulerianA n) :=
        hasPosLeadingCoeff_of_monic (generalizedEulerian_monic 1 _)
      have hA_deg : (eulerianA n).natDegree = n - 1 := generalizedEulerian_natDegree 1 _
      have hstrict : StrictInterl (eulerianA n) F := by
        refine strictInterl_of_eval_mul_derivative_nonpos hA_pos
          (generalizedEulerian_splits one_pos _)
          (generalizedEulerian_one_hasSimpleRoots _).roots_nodup hF_pos
          (by rw [hA_deg, hdeg]; omega) (by rw [hA_deg, hdeg]; omega) ?_
        intro r hr
        rw [hF, eval_finsetSum, Finset.sum_mul]
        refine Finset.sum_nonpos fun k _ => ?_
        rw [eval_smul, smul_eq_mul, mul_assoc]
        exact mul_nonpos_of_nonneg_of_nonpos (hc k)
          (b_eval_mul_derivative_nonpos hn.ne' (Nat.lt_succ_iff.mp k.isLt) hr)
      exact hstrict.2.1.2
  refine ⟨hF_ne, hsplits, hdeg, ?_, ?_⟩
  · rw [← hdeg]; exact (splits_iff_card_roots.mp hsplits)
  · intro r hr
    have hle := roots_nonpos_of_hasNonnegCoeffs hF_nonneg r hr
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have := (mem_roots hF_ne).mp hr
      rw [heq, IsRoot] at this
      linarith

/-- **Athanasiadis, Remark 7.2(b), Eulerian map `ℬ`.**  For every `n` and every
`c : Fin (n+1) → ℝ` with `c k ≥ 0` that is not identically zero,
`ℬ(∑_{k=0}^{n} c_k t^(n-k) (1+t)^k)` has only real roots. -/
theorem mathcalB_coneInput_splits (n : ℕ) (c : Fin (n + 1) → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hc0 : c ≠ 0) :
    (mathcalB (∑ k : Fin (n + 1), c k • (X ^ (n - (k : ℕ)) * (1 + X) ^ (k : ℕ)))).Splits :=
  (mathcalB_coneInput_realRooted n c hc hc0).2.1

end TypeBEulerian
