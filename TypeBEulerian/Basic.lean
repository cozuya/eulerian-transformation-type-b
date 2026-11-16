import RealRooted.CombinatorialExamples.TypeBEulerian

/-!
# The type B Eulerian transformation `ℬ`

Input polynomials live in `ℝ[X]` with the variable read as `t`; output polynomials live
in `ℝ[X]` with the variable read as `x`.

* `B n` is the type B Eulerian polynomial, defined by `B 0 = 1` and
  `B (n+1) = (1 + (2n+1)x) B n + 2x(1-x) (B n)'` (this is RealRooted's `typeBEulerian`;
  `B_succ` restates the recurrence in exactly this form).
* `mathcalB : ℝ[X] →ₗ[ℝ] ℝ[X]` is the real-linear map with `mathcalB (t^n) = B n`.
* `b n k = ∑_{j=0}^{k} (k choose j) • B (n-j)`, and `mathcalB_basis` proves
  `mathcalB (t^(n-k) (1+t)^k) = b n k` for `k ≤ n`.
-/

open Polynomial

noncomputable section

namespace TypeBEulerian

/-- The type B Eulerian polynomial `B_n` (RealRooted's `typeBEulerian`). -/
abbrev B (n : ℕ) : ℝ[X] := RealRooted.typeBEulerian n

theorem B_zero : B 0 = 1 := rfl

/-- The defining recurrence `B_{n+1} = (1 + (2n+1)x) B_n + 2x(1-x) B_n'`. -/
theorem B_succ (n : ℕ) :
    B (n + 1) = (1 + C (2 * (n : ℝ) + 1) * X) * B n +
      C 2 * X * (1 - X) * derivative (B n) := by
  rw [B, RealRooted.typeBEulerian_succ, RealRooted.typeBEulerianCoeffA,
    RealRooted.typeBEulerianCoeffB]

theorem B_one : B 1 = 1 + X := by
  rw [B_succ, B_zero]
  simp

theorem B_two : B 2 = 1 + 6 * X + X ^ 2 := by
  rw [B_succ, B_one]
  simp only [Nat.cast_one, derivative_add, derivative_one, derivative_X, zero_add, mul_one]
  norm_num [map_ofNat]
  ring

/-- The type B Eulerian transformation: the real-linear map with `t^n ↦ B_n`. -/
def mathcalB : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum fun n => LinearMap.toSpanSingleton ℝ ℝ[X] (B n)

theorem mathcalB_apply (p : ℝ[X]) :
    mathcalB p = p.sum fun n a => a • B n := by
  simp [mathcalB, Polynomial.lsum_apply, LinearMap.toSpanSingleton_apply]

theorem mathcalB_monomial (n : ℕ) (a : ℝ) : mathcalB (monomial n a) = a • B n := by
  rw [mathcalB_apply, sum_monomial_index]
  simp

/-- Basis behaviour: `ℬ(t^n) = B_n`. -/
theorem mathcalB_X_pow (n : ℕ) : mathcalB (X ^ n) = B n := by
  rw [← monomial_one_right_eq_X_pow, mathcalB_monomial, one_smul]

/-- `ℬ` sends a polynomial to the corresponding finite coefficient sum. -/
theorem mathcalB_eq_sum_range (p : ℝ[X]) :
    mathcalB p = ∑ m ∈ Finset.range (p.natDegree + 1), p.coeff m • B m := by
  rw [mathcalB_apply, sum_over_range]
  intro n
  simp

/-- The basis image `b(n,k) = ∑_{j=0}^{k} (k choose j) B_{n-j}`. -/
def b (n k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) • B (n - j)

/-- `ℬ(t^(n-k) (1+t)^k) = ∑_{j=0}^{k} (k choose j) B_{n-j}` for `k ≤ n`. -/
theorem mathcalB_basis {n k : ℕ} (hk : k ≤ n) :
    mathcalB (X ^ (n - k) * (1 + X) ^ k) = b n k := by
  have hexp : (X ^ (n - k) * (1 + X) ^ k : ℝ[X]) =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) • X ^ (n - k + i) := by
    rw [add_comm (1 : ℝ[X]) X, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one, pow_add, ← C_eq_natCast, smul_eq_C_mul]
    simp only [map_natCast]
    ring
  rw [hexp, map_sum, b, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < k + 1 := Finset.mem_range.mp hi
  rw [map_smul, mathcalB_X_pow, show k + 1 - 1 - i = k - i by omega,
    Nat.choose_symm (by omega), show n - k + (k - i) = n - i by omega]

/-- The input cone generator `t^(n-k) (1+t)^k`. -/
def basisInput (n k : ℕ) : ℝ[X] := X ^ (n - k) * (1 + X) ^ k

/-- The input polynomial `p(t) = ∑_{k=0}^{n} c_k t^(n-k) (1+t)^k`. -/
def coneInput (n : ℕ) (c : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ k : Fin (n + 1), c k • basisInput n k

/-- `ℬ(∑ c_k t^(n-k)(1+t)^k) = ∑ c_k b(n,k)`. -/
theorem mathcalB_coneInput (n : ℕ) (c : Fin (n + 1) → ℝ) :
    mathcalB (coneInput n c) = ∑ k : Fin (n + 1), c k • b n k := by
  rw [coneInput, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, basisInput, mathcalB_basis (Nat.lt_succ_iff.mp k.isLt)]

/-! ### Small cases -/

theorem b_zero_zero : b 0 0 = 1 := by
  simp [b]

theorem b_one_zero : b 1 0 = 1 + X := by
  simp [b, B_one]

theorem b_one_one : b 1 1 = 2 + X := by
  simp [b, Finset.sum_range_succ, B_one]
  ring

theorem b_two_zero : b 2 0 = 1 + 6 * X + X ^ 2 := by
  simp [b, B_two]

theorem b_two_one : b 2 1 = 2 + 7 * X + X ^ 2 := by
  simp [b, Finset.sum_range_succ, B_two, B_one]
  ring

theorem b_two_two : b 2 2 = 4 + 8 * X + X ^ 2 := by
  simp [b, Finset.sum_range_succ, B_two, B_one, two_smul]
  ring

end TypeBEulerian
