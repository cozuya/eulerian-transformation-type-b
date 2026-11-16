import TypeBEulerian.Basic
import RealRooted.PolynomialValueEulerNumerator

/-!
# Type B Eulerian polynomials as Euler numerators

* `B_coe_eq`: `B_l(x) = (1-x)^(l+1) ∑_{m ≥ 0} (2m+1)^l x^m` (formal power series).
* `eulerNumerator_coe_eq`: if `natDegree q = n`, then RealRooted's canonical Euler numerator
  `E[q]` equals `(1-x)^(n+1) ∑_{m ≥ 0} q(m) x^m`.
* `shiftedInput n k s = (2t+1)^(n-k) ((1-s)(2t+1)+1)^k`, a polynomial in `t` for a fixed
  real parameter `s`.
* `eval_eulerNumerator_shiftedInput`: for `s ≠ 1`,
  `E[shiftedInput n k s](s) = (1-s)^k b(n,k)(s)`, where `E` is RealRooted's canonical Euler
  numerator `polynomialValueEulerNumerator`.
-/

open Polynomial

noncomputable section

namespace TypeBEulerian

open RealRooted

/-- The value series `∑_m (2m+1)^l x^m`. -/
def oddPowSeries (l : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun m : ℕ => (2 * (m : ℝ) + 1) ^ l

private theorem oddPowSeries_succ (l : ℕ) :
    oddPowSeries (l + 1) =
      oddPowSeries l + 2 * PowerSeries.X * PowerSeries.derivative (R := ℝ) (oddPowSeries l) := by
  ext m
  rw [map_add, mul_assoc, (map_ofNat (PowerSeries.C (R := ℝ)) 2).symm,
    PowerSeries.coeff_C_mul]
  simp only [oddPowSeries, PowerSeries.coeff_mk]
  rcases m with _ | m
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
    push_cast
    ring

/-- `B_l = (1-x)^(l+1) ∑_m (2m+1)^l x^m` as formal power series. -/
theorem B_coe_eq (l : ℕ) :
    ((B l : ℝ[X]) : PowerSeries ℝ) = (1 - PowerSeries.X) ^ (l + 1) * oddPowSeries l := by
  induction l with
  | zero =>
      rw [B_zero, Polynomial.coe_one, zero_add, pow_one, mul_comm]
      have h : oddPowSeries 0 = PowerSeries.mk 1 := by
        unfold oddPowSeries
        congr 1
      rw [h, PowerSeries.mk_one_mul_one_sub_eq_one]
  | succ l ih =>
      rw [B_succ]
      simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
        Polynomial.coe_one, Polynomial.coe_sub, ← PowerSeries.derivative_coe, ih,
        oddPowSeries_succ, Derivation.leibniz, Derivation.leibniz_pow, map_sub,
        Derivation.map_one_eq_zero, PowerSeries.derivative_X, smul_eq_mul]
      have h2 : (PowerSeries.C (2 : ℝ)) = (2 : PowerSeries ℝ) := map_ofNat _ 2
      have h21 : (PowerSeries.C (2 * (l : ℝ) + 1)) = 2 * (l : PowerSeries ℝ) + 1 := by
        rw [map_add, map_mul, map_natCast, h2, map_one]
      rw [h2, h21]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
      ring

/-- For `natDegree q = n`, the canonical Euler numerator is `(1-x)^(n+1)` times the value
series of `q`. -/
theorem eulerNumerator_coe_eq {q : ℝ[X]} {n : ℕ} (hq : q.natDegree = n) :
    ((polynomialValueEulerNumerator q : ℝ[X]) : PowerSeries ℝ) =
      (1 - PowerSeries.X) ^ (n + 1) * PowerSeries.mk (polynomialValueSeq q) := by
  rw [polynomialValueSeries_eq_eulerNumerator_mul_invOneSubPow, hq]
  have h := PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℝ 0 (n + 1)
  rw [zero_add] at h
  calc ((polynomialValueEulerNumerator q : ℝ[X]) : PowerSeries ℝ)
      = (polynomialValueEulerNumerator q : PowerSeries ℝ) *
          ((1 - PowerSeries.X) ^ (n + 1) * (PowerSeries.invOneSubPow ℝ (n + 1)).val) := by
        rw [h]; simp [PowerSeries.invOneSubPow]
    _ = _ := by ring

/-- The parametrized input `(2t+1)^(n-k) ((1-s)(2t+1)+1)^k`. -/
def shiftedInput (n k : ℕ) (s : ℝ) : ℝ[X] :=
  (C 2 * X + 1) ^ (n - k) * (C (1 - s) * (C 2 * X + 1) + 1) ^ k

theorem shiftedInput_eq_sum {n k : ℕ} (hk : k ≤ n) (s : ℝ) :
    shiftedInput n k s =
      ∑ j ∈ Finset.range (k + 1),
        C ((k.choose j : ℝ) * (1 - s) ^ (k - j)) * (C 2 * X + 1) ^ (n - j) := by
  rw [shiftedInput, add_pow (C (1 - s) * (C 2 * X + 1)) 1 k, Finset.mul_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < k + 1 := Finset.mem_range.mp hi
  rw [show k + 1 - 1 - i = k - i by omega, one_pow, mul_one, Nat.choose_symm (by omega), mul_pow,
    ← C_pow, C_mul, ← C_eq_natCast]
  have hpow : (C 2 * X + 1 : ℝ[X]) ^ (n - i) =
      (C 2 * X + 1) ^ (n - k) * (C 2 * X + 1) ^ (k - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  simp only [map_natCast]
  ring

theorem natDegree_shiftedInput (n k : ℕ) {s : ℝ} (hs : s ≠ 1) :
    (shiftedInput n k s).natDegree = n - k + k := by
  have h1 : (C 2 * X + 1 : ℝ[X]).natDegree = 1 := by
    rw [show (C 2 * X + 1 : ℝ[X]) = C 2 * X + C 1 by simp]
    exact natDegree_linear (by norm_num)
  have h2 : (C (1 - s) * (C 2 * X + 1) + 1 : ℝ[X]).natDegree = 1 := by
    rw [show (C (1 - s) * (C 2 * X + 1) + 1 : ℝ[X]) = C ((1 - s) * 2) * X + C (1 - s + 1) by
      simp only [C_mul, C_add, C_1]; ring]
    exact natDegree_linear (mul_ne_zero (sub_ne_zero.mpr hs.symm) (by norm_num))
  have hne1 : (C 2 * X + 1 : ℝ[X]) ≠ 0 := fun h => by rw [h, natDegree_zero] at h1; exact zero_ne_one h1
  have hne2 : (C (1 - s) * (C 2 * X + 1) + 1 : ℝ[X]) ≠ 0 := fun h => by
    rw [h, natDegree_zero] at h2; exact zero_ne_one h2
  rw [shiftedInput, natDegree_mul (pow_ne_zero _ hne1) (pow_ne_zero _ hne2), natDegree_pow,
    natDegree_pow, h1, h2, mul_one, mul_one]

/-- The Euler numerator of the shifted input, as an explicit polynomial in `x`. -/
theorem eulerNumerator_shiftedInput {n k : ℕ} (hk : k ≤ n) {s : ℝ} (hs : s ≠ 1) :
    polynomialValueEulerNumerator (shiftedInput n k s) =
      ∑ j ∈ Finset.range (k + 1),
        C ((k.choose j : ℝ) * (1 - s) ^ (k - j)) * (1 - X) ^ j * B (n - j) := by
  apply Polynomial.coe_injective ℝ
  rw [eulerNumerator_coe_eq (natDegree_shiftedInput n k hs), Nat.sub_add_cancel hk]
  have hseq : PowerSeries.mk (polynomialValueSeq (shiftedInput n k s)) =
      ∑ j ∈ Finset.range (k + 1),
        PowerSeries.C ((k.choose j : ℝ) * (1 - s) ^ (k - j)) * oddPowSeries (n - j) := by
    ext m
    rw [PowerSeries.coeff_mk, polynomialValueSeq_apply, shiftedInput_eq_sum hk, eval_finsetSum,
      map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_C_mul, oddPowSeries, PowerSeries.coeff_mk]
    simp
  rw [hseq, Finset.mul_sum, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hk
  rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
    Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, B_coe_eq,
    show n + 1 = j + (n - j + 1) by omega, pow_add]
  ring

/-- The pointwise identity `E[q_s](s) = (1-s)^k b(n,k)(s)`. -/
theorem eval_eulerNumerator_shiftedInput {n k : ℕ} (hk : k ≤ n) {s : ℝ} (hs : s ≠ 1) :
    (polynomialValueEulerNumerator (shiftedInput n k s)).eval s = (1 - s) ^ k * (b n k).eval s := by
  rw [eulerNumerator_shiftedInput hk hs, eval_finsetSum, b, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, eval_smul, smul_eq_mul]
  rw [show (1 - s) ^ k = (1 - s) ^ (k - j) * (1 - s) ^ j by rw [← pow_add]; congr 1; omega]
  ring

end TypeBEulerian
