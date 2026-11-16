import TypeBEulerian.EulerNumerator
import RealRooted.GeneralizedEulerian
import RealRooted.PolynomialValueEulerNumerator.Interlacing
import RealRooted.MaWang.CriticalSign
import RealRooted.Interlacing.OuterDifference
import RealRooted.SimpleRoots

/-!
# The ordinary Eulerian polynomial is a common interlacer

Write `eulerianA n` for the ordinary Eulerian polynomial `A_n`, `n ≥ 1`, realized as
RealRooted's `generalizedEulerian 1 (n - 1)` (recurrence
`A_{m+1} = (1 + m x) A_m + x(1-x) A_m'`, `A_1 = 1`).

* `eulerNumerator_X_add_one_pow`: `A_n` is the canonical Euler numerator of `(t+1)^n`.
* `generalizedEulerian_one_hasSimpleRoots`, `generalizedEulerian_one_root_neg`: `A_n` has
  simple roots, and they are negative.
* `b_eval_mul_derivative_nonpos`: at every root `r` of `A_n`,
  `b(n,k)(r) · A_n'(r) ≤ 0` for every `k ≤ n`.

The last statement combines Brändén's Theorem 4.6 (RealRooted's
`polynomialValueEulerNumerator_strictInterl_of_rootwiseLE`), applied to `(t+1)^n` and the
monic rescaling of `shiftedInput n k r`, with the pointwise identity
`E[shiftedInput n k r](r) = (1-r)^k b(n,k)(r)`.
-/

open Polynomial

noncomputable section

namespace TypeBEulerian

open RealRooted

/-- The ordinary Eulerian polynomial `A_n` for `n ≥ 1` (`A_1 = 1`, `A_2 = 1 + x`, ...). -/
abbrev eulerianA (n : ℕ) : ℝ[X] := generalizedEulerian 1 (n - 1)

/-- The value series `∑_j (j+1)^l x^j`. -/
def succPowSeries (l : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun j : ℕ => ((j : ℝ) + 1) ^ l

private theorem succPowSeries_succ (l : ℕ) :
    succPowSeries (l + 1) =
      succPowSeries l + PowerSeries.X * PowerSeries.derivative (R := ℝ) (succPowSeries l) := by
  ext m
  rw [map_add]
  simp only [succPowSeries, PowerSeries.coeff_mk]
  rcases m with _ | m
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
    push_cast
    ring

/-- `generalizedEulerian 1 m = (1-x)^(m+2) ∑_j (j+1)^(m+1) x^j` as formal power series. -/
theorem generalizedEulerian_one_coe_eq (m : ℕ) :
    ((generalizedEulerian 1 m : ℝ[X]) : PowerSeries ℝ) =
      (1 - PowerSeries.X) ^ (m + 2) * succPowSeries (m + 1) := by
  induction m with
  | zero =>
      have h := PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℝ 0 2
      rw [zero_add, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose] at h
      have hs : succPowSeries 1 = PowerSeries.mk fun n => ((1 + n).choose 1 : ℝ) := by
        unfold succPowSeries
        congr 1
        funext j
        simp [add_comm]
      rw [hs, h]
      simp [generalizedEulerian, PowerSeries.invOneSubPow]
  | succ m ih =>
      rw [generalizedEulerian_succ]
      simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
        Polynomial.coe_one, Polynomial.coe_sub, ← PowerSeries.derivative_coe, ih,
        succPowSeries_succ (m + 1), Derivation.leibniz, Derivation.leibniz_pow, map_sub,
        Derivation.map_one_eq_zero, PowerSeries.derivative_X, smul_eq_mul]
      have h1 : (PowerSeries.C (1 : ℝ)) = (1 : PowerSeries ℝ) := map_one _
      have h21 : (PowerSeries.C (1 * (m : ℝ) + 1)) = (m : PowerSeries ℝ) + 1 := by
        rw [one_mul, map_add, map_natCast, map_one]
      rw [h1, h21]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat,
        show m + 2 - 1 = m + 1 by omega]
      ring

/-- `A_{m+1}` is the canonical Euler numerator of `(t+1)^(m+1)`. -/
theorem eulerNumerator_X_add_one_pow (m : ℕ) :
    polynomialValueEulerNumerator ((X + 1) ^ (m + 1) : ℝ[X]) = generalizedEulerian 1 m := by
  have hdeg : ((X + 1) ^ (m + 1) : ℝ[X]).natDegree = m + 1 := by
    rw [natDegree_pow, show (X + 1 : ℝ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
  apply Polynomial.coe_injective ℝ
  rw [eulerNumerator_coe_eq hdeg, generalizedEulerian_one_coe_eq]
  congr 1
  ext j
  simp [succPowSeries, polynomialValueSeq_apply]

theorem generalizedEulerian_one_root_neg {m : ℕ} {r : ℝ}
    (hr : (generalizedEulerian 1 m).IsRoot r) : r < 0 := by
  have hnonneg := (generalizedEulerian_invariants (c := 1) one_pos m).2.1
  have hne : generalizedEulerian 1 m ≠ 0 := (generalizedEulerian_monic 1 m).ne_zero
  have hle : r ≤ 0 :=
    roots_nonpos_of_hasNonnegCoeffs hnonneg r ((mem_roots hne).mpr hr)
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    rw [heq, IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero_generalizedEulerian] at hr
    exact one_ne_zero hr

/-- The ordinary Eulerian polynomials have simple roots. -/
theorem generalizedEulerian_one_hasSimpleRoots : ∀ m : ℕ,
    HasSimpleRoots (generalizedEulerian 1 m)
  | 0 => by
      intro r hr
      simp [generalizedEulerian, IsRoot] at hr
  | m + 1 => by
      have ih := generalizedEulerian_one_hasSimpleRoots m
      have hpos : ∀ j, HasPosLeadingCoeff (generalizedEulerian 1 j) := fun j =>
        hasPosLeadingCoeff_of_monic (generalizedEulerian_monic 1 j)
      refine (strictInterl_package_of_eval_mul_derivative_neg_succ
        (generalizedEulerian_splits one_pos m) (hpos m) (hpos (m + 1))
        (generalizedEulerian_natDegree 1 m) (generalizedEulerian_natDegree 1 (m + 1))
        ?_).2.2.2.2.1
      intro r hr
      have hr0 : r < 0 := generalizedEulerian_one_root_neg hr
      have hd : (generalizedEulerian 1 m).derivative.eval r ≠ 0 :=
        ih.eval_derivative_ne_zero hr
      have hval : (generalizedEulerian 1 (m + 1)).eval r =
          r * (1 - r) * (generalizedEulerian 1 m).derivative.eval r := by
        rw [generalizedEulerian_succ]
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, eval_sub, hr.eq_zero]
        ring
      rw [hval]
      have hsq : 0 < (generalizedEulerian 1 m).derivative.eval r ^ 2 := by positivity
      have hrr : r * (1 - r) < 0 := by nlinarith
      have hprod := mul_neg_of_neg_of_pos hrr hsq
      linarith [show r * (1 - r) * (generalizedEulerian 1 m).derivative.eval r *
          (generalizedEulerian 1 m).derivative.eval r =
        r * (1 - r) * (generalizedEulerian 1 m).derivative.eval r ^ 2 by ring]

/-- The coefficient of `x^n` in `E[shiftedInput n k s]` is `(-s)^k` (for `s ≠ 1`). Since
`E[shiftedInput n k s]` has degree at most `n`, for `s < 0` this is its positive leading
coefficient. -/
theorem coeff_eulerNumerator_shiftedInput {n k : ℕ} (hk : k ≤ n) {s : ℝ} (hs : s ≠ 1) :
    (polynomialValueEulerNumerator (shiftedInput n k s)).coeff n = (-s) ^ k := by
  rw [eulerNumerator_shiftedInput hk hs, finsetSum_coeff]
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (C ((k.choose j : ℝ) * (1 - s) ^ (k - j)) * (1 - X) ^ j * B (n - j)).coeff n =
        (-1) ^ j * (1 - s) ^ (k - j) * (k.choose j : ℝ) := by
    intro j hj
    have hj' : j ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hk
    have h1X : ((1 : ℝ[X]) - X).natDegree ≤ 1 := by
      rw [show ((1 : ℝ[X]) - X) = C (-1) * X + C 1 by simp; ring]
      exact natDegree_linear_le
    have hpow : (((1 : ℝ[X]) - X) ^ j).coeff j = (-1) ^ j := by
      have := coeff_pow_of_natDegree_le (m := j) h1X
      rw [mul_one] at this
      rw [this]
      simp [coeff_one]
    have hdeg1 : (((1 : ℝ[X]) - X) ^ j).natDegree ≤ j :=
      natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left j h1X)
    have hdegB : (B (n - j)).natDegree ≤ n - j := (RealRooted.natDegree_typeBEulerian _).le
    have hcoeff := coeff_mul_add_eq_of_natDegree_le hdeg1 hdegB
    rw [show j + (n - j) = n by omega] at hcoeff
    have htop : (B (n - j)).coeff (n - j) = 1 := (RealRooted.coeff_typeBEulerian_top_and_above _).1
    rw [mul_assoc, coeff_C_mul, hcoeff, hpow, htop]
    ring
  rw [Finset.sum_congr rfl hterm, show -s = -1 + (1 - s) by ring, add_pow]

/-! ### Brändén's theorem for the shifted inputs -/

/-- `shiftRoot s = (2-s)/(2(1-s))`; the second factor of `shiftedInput n k s` vanishes at
`t = -shiftRoot s`. -/
def shiftRoot (s : ℝ) : ℝ := (2 - s) / (2 * (1 - s))

/-- The monic rescaling `(t + 1/2)^(n-k) (t + shiftRoot s)^k` of `shiftedInput n k s`. -/
def shiftedMonic (n k : ℕ) (s : ℝ) : ℝ[X] :=
  (X + C (1 / 2)) ^ (n - k) * (X + C (shiftRoot s)) ^ k

theorem shiftedInput_eq_C_mul (n k : ℕ) {s : ℝ} (hs : s ≠ 1) :
    shiftedInput n k s = C (2 ^ (n - k) * (2 * (1 - s)) ^ k) * shiftedMonic n k s := by
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr hs.symm
  have e1 : (C 2 * X + 1 : ℝ[X]) = C 2 * (X + C (1 / 2)) := by
    rw [mul_add, ← C_mul]; norm_num
  have ha : 2 * (1 - s) * shiftRoot s = 2 - s := by
    rw [shiftRoot]; field_simp
  have e2 : (C (1 - s) * (C 2 * X + 1) + 1 : ℝ[X]) =
      C (2 * (1 - s)) * (X + C (shiftRoot s)) := by
    rw [mul_add (C (2 * (1 - s))), ← C_mul, ha, C_mul, C_sub, C_sub, C_1]
    simp only [map_ofNat]
    ring
  rw [shiftedInput, shiftedMonic, e2, e1, mul_pow, mul_pow]
  simp only [map_mul, map_pow]
  ring

theorem shiftedMonic_monic (n k : ℕ) (s : ℝ) : (shiftedMonic n k s).Monic :=
  ((monic_X_add_C _).pow _).mul ((monic_X_add_C _).pow _)

theorem shiftedMonic_splits (n k : ℕ) (s : ℝ) : (shiftedMonic n k s).Splits :=
  ((Splits.X_add_C _).pow _).mul ((Splits.X_add_C _).pow _)

theorem natDegree_shiftedMonic {n k : ℕ} (hk : k ≤ n) (s : ℝ) :
    (shiftedMonic n k s).natDegree = n := by
  rw [shiftedMonic, ((monic_X_add_C _).pow _).natDegree_mul ((monic_X_add_C _).pow _),
    (monic_X_add_C _).natDegree_pow, (monic_X_add_C _).natDegree_pow, natDegree_X_add_C,
    natDegree_X_add_C]
  omega

theorem shiftedMonic_roots_mem_Icc {n k : ℕ} {s : ℝ} (hs : s ≤ 0) :
    ∀ r ∈ (shiftedMonic n k s).roots, -1 ≤ r ∧ r ≤ 0 := by
  intro r hr
  have hroot : (shiftedMonic n k s).IsRoot r :=
    (mem_roots (shiftedMonic_monic n k s).ne_zero).mp hr
  have h1s : 0 < 1 - s := by linarith
  have hlo : 1 / 2 ≤ shiftRoot s := by
    rw [shiftRoot, le_div_iff₀ (by positivity)]; linarith
  have hhi : shiftRoot s ≤ 1 := by
    rw [shiftRoot, div_le_iff₀ (by positivity)]; linarith
  simp only [shiftedMonic, IsRoot, eval_mul, eval_pow, eval_add, eval_X, eval_C,
    mul_eq_zero, pow_eq_zero_iff', ne_eq] at hroot
  rcases hroot with ⟨h, _⟩ | ⟨h, _⟩ <;> constructor <;> linarith

private theorem forall₂_le_of_forall_le :
    ∀ {l₁ l₂ : List ℝ}, l₁.length = l₂.length → (∀ x ∈ l₁, ∀ y ∈ l₂, x ≤ y) →
      List.Forall₂ (· ≤ ·) l₁ l₂
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: l₁, y :: l₂, h, hle =>
      List.Forall₂.cons (hle x (by simp) y (by simp))
        (forall₂_le_of_forall_le (by simpa using h)
          fun a ha b hb => hle a (by simp [ha]) b (by simp [hb]))

/-- `(t+1)^n` is rootwise below every degree-`n` split polynomial with roots `≥ -1`. -/
theorem rootwiseLE_X_add_one_pow {g : ℝ[X]} {n : ℕ} (hg : g.Splits) (hdeg : g.natDegree = n)
    (hroots : ∀ r ∈ g.roots, -1 ≤ r) : RootwiseLE ((X + 1) ^ n) g := by
  have hf : ((X + 1 : ℝ[X]) ^ n).Splits := by
    simpa using (Splits.X_add_C (1 : ℝ)).pow n
  have hfdeg : ((X + 1 : ℝ[X]) ^ n).natDegree = n := by
    rw [natDegree_pow, show (X + 1 : ℝ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
  have hfne : ((X + 1 : ℝ[X]) ^ n) ≠ 0 := pow_ne_zero _ (by
    rw [show (X + 1 : ℝ[X]) = X + C 1 by simp]; exact X_add_C_ne_zero 1)
  unfold RootwiseLE
  apply forall₂_le_of_forall_le
  · rw [Multiset.length_sort, Multiset.length_sort, ← hf.natDegree_eq_card_roots,
      ← hg.natDegree_eq_card_roots, hfdeg, hdeg]
  · intro x hx y hy
    rw [Multiset.mem_sort] at hx hy
    have hxroot := (mem_roots hfne).mp hx
    simp only [IsRoot, eval_pow, eval_add, eval_X, eval_one, pow_eq_zero_iff', ne_eq] at hxroot
    have hx' : x = -1 := by linarith [hxroot.1]
    rw [hx']
    exact hroots y hy

/-- Brändén's theorem: `A_n` interlaces the Euler numerator of every shifted input with `s ≤ 0`. -/
theorem strictInterl_eulerianA_eulerNumerator_shiftedInput {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ n)
    {s : ℝ} (hs : s ≤ 0) :
    StrictInterl (eulerianA n) (polynomialValueEulerNumerator (shiftedInput n k s)) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hκ : (2 : ℝ) ^ (n - k) * (2 * (1 - s)) ^ k ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ two_ne_zero)
    exact pow_ne_zero _ (mul_ne_zero two_ne_zero (by linarith))
  have hf_monic : ((X + 1 : ℝ[X]) ^ n).Monic := by
    rw [show (X + 1 : ℝ[X]) = X + C 1 by simp]; exact (monic_X_add_C 1).pow n
  have hf_splits : ((X + 1 : ℝ[X]) ^ n).Splits := by
    simpa using (Splits.X_add_C (1 : ℝ)).pow n
  have hf_deg : ((X + 1 : ℝ[X]) ^ n).natDegree = n := by
    rw [natDegree_pow, show (X + 1 : ℝ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
  have hf_roots : ∀ r ∈ ((X + 1 : ℝ[X]) ^ n).roots, -1 ≤ r ∧ r ≤ 0 := by
    intro r hr
    have hne : ((X + 1 : ℝ[X]) ^ n) ≠ 0 := hf_monic.ne_zero
    have hroot := (mem_roots hne).mp hr
    simp only [IsRoot, eval_pow, eval_add, eval_X, eval_one, pow_eq_zero_iff', ne_eq] at hroot
    constructor <;> linarith [hroot.1]
  have hg_roots := shiftedMonic_roots_mem_Icc (n := n) (k := k) hs
  have hB := polynomialValueEulerNumerator_strictInterl_of_rootwiseLE hf_monic
    (shiftedMonic_monic n k s) hf_splits (shiftedMonic_splits n k s) hf_deg
    (natDegree_shiftedMonic hk s) hn hf_roots hg_roots
    (rootwiseLE_X_add_one_pow (shiftedMonic_splits n k s) (natDegree_shiftedMonic hk s)
      fun r hr => (hg_roots r hr).1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [eulerNumerator_X_add_one_pow] at hB
  rw [shiftedInput_eq_C_mul _ _ hs1, polynomialValueEulerNumerator_C_mul hκ]
  simpa [eulerianA] using hB.C_mul_right hκ

/-- **Signs at the common interlacer.**  For `n ≥ 1`, `k ≤ n` and every root `r` of the
ordinary Eulerian polynomial `A_n`, `b(n,k)(r) · A_n'(r) ≤ 0`. -/
theorem b_eval_mul_derivative_nonpos {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ n) {r : ℝ}
    (hr : (eulerianA n).IsRoot r) :
    (b n k).eval r * (eulerianA n).derivative.eval r ≤ 0 := by
  have hr0 : r < 0 := generalizedEulerian_one_root_neg hr
  have hr1 : r ≠ 1 := by intro h; rw [h] at hr0; norm_num at hr0
  set F := polynomialValueEulerNumerator (shiftedInput n k r) with hF
  have hFdeg_le : F.natDegree ≤ n := by
    have := natDegree_polynomialValueEulerNumerator_le (shiftedInput n k r)
    rwa [natDegree_shiftedInput n k hr1, Nat.sub_add_cancel hk] at this
  have hFcoeff : F.coeff n = (-r) ^ k := coeff_eulerNumerator_shiftedInput hk hr1
  have hFcoeff_pos : 0 < F.coeff n := by rw [hFcoeff]; exact pow_pos (by linarith) k
  have hFdeg : F.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hFdeg_le hFcoeff_pos.ne'
  have hF_pos : HasPosLeadingCoeff F := by
    rw [HasPosLeadingCoeff, leadingCoeff, hFdeg]; exact hFcoeff_pos
  have hA_pos : HasPosLeadingCoeff (eulerianA n) :=
    hasPosLeadingCoeff_of_monic (generalizedEulerian_monic 1 _)
  have hsign := (strictInterl_eulerianA_eulerNumerator_shiftedInput hn hk hr0.le
    ).eval_mul_derivative_nonpos_of_left_root hA_pos hF_pos hr
  rw [eval_eulerNumerator_shiftedInput hk hr1, mul_assoc] at hsign
  have hpos : 0 < (1 - r) ^ k := pow_pos (by linarith) k
  by_contra hcon
  linarith [mul_pos hpos (lt_of_not_ge hcon)]

end TypeBEulerian
