import TypeBEulerian

/-!
# Independent restatement of the verified results

The statements below use only Mathlib notions. Instead of the project's definitions, they
quantify over

* any sequence `P : ℕ → ℝ[X]` with `P 0 = 1` and
  `P (n+1) = (1 + (2n+1)x) P n + 2x(1-x) (P n)'` (the type B Eulerian polynomials), and
* any `ℝ`-linear map `L : ℝ[X] →ₗ[ℝ] ℝ[X]` with `L (X ^ m) = P m` for every `m`
  (the type B Eulerian transformation `ℬ`).

`sequence_exists` and `map_exists` show that such `P` and `L` exist, so the hypotheses are
not vacuous. Each statement is proved directly from the project's theorems. `verify.sh`
checks the printed types and transitive axioms below.
-/

open Polynomial

set_option autoImplicit false

namespace TypeBEulerianVerification

/-- The type B Eulerian recurrence. -/
def IsTypeBEulerian (P : ℕ → ℝ[X]) : Prop :=
  P 0 = 1 ∧ ∀ n : ℕ, P (n + 1) =
    (1 + C (2 * (n : ℝ) + 1) * X) * P n + C 2 * X * (1 - X) * derivative (P n)

theorem eq_B {P : ℕ → ℝ[X]} (hP : IsTypeBEulerian P) : ∀ n, P n = TypeBEulerian.B n
  | 0 => hP.1
  | n + 1 => by rw [hP.2, eq_B hP n, TypeBEulerian.B_succ]

theorem eq_mathcalB {P : ℕ → ℝ[X]} (hP : IsTypeBEulerian P) (L : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hL : ∀ m, L (X ^ m) = P m) : L = TypeBEulerian.mathcalB := by
  apply Polynomial.lhom_ext'
  intro m
  apply LinearMap.ext_ring
  simp only [LinearMap.coe_comp, Function.comp_apply, monomial_one_right_eq_X_pow]
  rw [hL, eq_B hP, TypeBEulerian.mathcalB_X_pow]

/-- Such a sequence exists, and it starts `1, 1 + x, 1 + 6x + x²`. -/
theorem sequence_exists :
    ∃ P : ℕ → ℝ[X], IsTypeBEulerian P ∧ P 1 = 1 + X ∧ P 2 = 1 + 6 * X + X ^ 2 :=
  ⟨TypeBEulerian.B, ⟨TypeBEulerian.B_zero, TypeBEulerian.B_succ⟩, TypeBEulerian.B_one,
    TypeBEulerian.B_two⟩

/-- Such a linear map exists. -/
theorem map_exists {P : ℕ → ℝ[X]} (hP : IsTypeBEulerian P) :
    ∃ L : ℝ[X] →ₗ[ℝ] ℝ[X], ∀ m, L (X ^ m) = P m :=
  ⟨TypeBEulerian.mathcalB, fun m => by rw [TypeBEulerian.mathcalB_X_pow, eq_B hP]⟩

/-- The basis images: `ℬ(t^(n-k) (1+t)^k) = ∑_{j=0}^{k} (k choose j) B_{n-j}` for `k ≤ n`. -/
theorem basis_image {P : ℕ → ℝ[X]} (hP : IsTypeBEulerian P) (L : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hL : ∀ m, L (X ^ m) = P m) {n k : ℕ} (hk : k ≤ n) :
    L (X ^ (n - k) * (1 + X) ^ k) = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) • P (n - j) := by
  rw [eq_mathcalB hP L hL, TypeBEulerian.mathcalB_basis hk, TypeBEulerian.b]
  simp only [eq_B hP]

/-- **Athanasiadis, Remark 7.2(b), Eulerian map.** For every `n` and every nonnegative,
not identically zero `c`, `ℬ(∑_k c_k t^(n-k) (1+t)^k)` has only real roots. -/
theorem real_rooted {P : ℕ → ℝ[X]} (hP : IsTypeBEulerian P) (L : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hL : ∀ m, L (X ^ m) = P m) (n : ℕ) (c : Fin (n + 1) → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hc0 : c ≠ 0) :
    (L (∑ k : Fin (n + 1), c k • (X ^ (n - (k : ℕ)) * (1 + X) ^ (k : ℕ)))).Splits := by
  rw [eq_mathcalB hP L hL]
  exact TypeBEulerian.mathcalB_coneInput_splits n c hc hc0

/-- Strong form: the image is nonzero, has degree `n`, has `n` real roots counted with
multiplicity, and all of them are strictly negative. -/
theorem real_rooted_strong {P : ℕ → ℝ[X]} (hP : IsTypeBEulerian P) (L : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hL : ∀ m, L (X ^ m) = P m) (n : ℕ) (c : Fin (n + 1) → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hc0 : c ≠ 0) :
    let p := L (∑ k : Fin (n + 1), c k • (X ^ (n - (k : ℕ)) * (1 + X) ^ (k : ℕ)))
    p ≠ 0 ∧ p.Splits ∧ p.natDegree = n ∧ p.roots.card = n ∧ ∀ r ∈ p.roots, r < 0 := by
  rw [eq_mathcalB hP L hL]
  exact TypeBEulerian.mathcalB_coneInput_realRooted n c hc hc0

/-- The all-zero coefficient vector gives the zero polynomial. -/
theorem zero_vector (L : ℝ[X] →ₗ[ℝ] ℝ[X]) (n : ℕ) :
    L (∑ k : Fin (n + 1), (0 : ℝ) • (X ^ (n - (k : ℕ)) * (1 + X) ^ (k : ℕ))) = 0 := by
  simp

/-- For `n = 0` the image is the constant `c 0`. -/
theorem degree_zero {P : ℕ → ℝ[X]} (hP : IsTypeBEulerian P) (L : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hL : ∀ m, L (X ^ m) = P m) (c : Fin 1 → ℝ) :
    L (∑ k : Fin 1, c k • (X ^ (0 - (k : ℕ)) * (1 + X) ^ (k : ℕ))) = C (c 0) := by
  rw [eq_mathcalB hP L hL]
  exact TypeBEulerian.mathcalB_coneInput_n_zero c

end TypeBEulerianVerification

#check @TypeBEulerianVerification.real_rooted
#check @TypeBEulerianVerification.real_rooted_strong
#check @TypeBEulerianVerification.zero_vector
#check @TypeBEulerianVerification.degree_zero
#check @TypeBEulerianVerification.basis_image
#check @TypeBEulerianVerification.sequence_exists
#check @TypeBEulerianVerification.map_exists
#check @TypeBEulerian.mathcalB_coneInput_splits
#check @TypeBEulerian.mathcalB_coneInput_realRooted

#print axioms TypeBEulerianVerification.real_rooted
#print axioms TypeBEulerianVerification.real_rooted_strong
#print axioms TypeBEulerianVerification.zero_vector
#print axioms TypeBEulerianVerification.degree_zero
#print axioms TypeBEulerianVerification.basis_image
#print axioms TypeBEulerianVerification.sequence_exists
#print axioms TypeBEulerianVerification.map_exists
#print axioms TypeBEulerian.mathcalB_coneInput_splits
#print axioms TypeBEulerian.mathcalB_coneInput_realRooted
#print axioms TypeBEulerian.mathcalB_coneInput_zero
#print axioms TypeBEulerian.mathcalB_coneInput_n_zero
#print axioms TypeBEulerian.b_eval_mul_derivative_nonpos
