import LeanLab.ChenDoubleSieve.Statements

/-!
# Wu 2004 Section 7: algebra after the analytic estimates

Source: https://arxiv.org/pdf/0705.1652, pages 30 and 31, equations 7.3 and 7.4.
The matrix and sieve estimates are inputs. This file does not certify Table 1.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Wu04Numerics
open Finset Matrix

/-- A matrix with nonnegative entries preserves coordinate inequalities. -/
theorem mulVec_mono {n : Type*} [Fintype n] (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j) {u v : n → ℝ} (huv : ∀ i, u i ≤ v i) :
    ∀ i, (C *ᵥ u) i ≤ (C *ᵥ v) i := by
  intro i
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (huv j) (hC i j)

/-- The comparison step from equations 7.3 and 7.4.
`C` is a nonnegative left inverse of `I-A`. -/
theorem section7_comparison {n : Type*} [Fintype n] [DecidableEq n]
    (A C : Matrix n n ℝ) (B H X : n → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hleft : C * (1 - A) = 1)
    (hH : ∀ i, B i ≤ ((1 - A) *ᵥ H) i)
    (hX : (1 - A) *ᵥ X = B) : ∀ i, X i ≤ H i := by
  have h := mulVec_mono C hC hH
  rw [← hX] at h
  simpa only [mulVec_mulVec, hleft, one_mulVec] using h

/-- Exact slack in the final displayed estimate on page 31. -/
theorem printed_constant_slack :
    (782085 / 100000 : ℝ) - 8 * (1 - 223938 / 10000000) = 1 / 2500000 := by
  norm_num

/-- The final arithmetic implication, with arbitrary nonnegative normalizer. -/
theorem printed_constant_of_bound {d θ x : ℝ} (hθ : 0 ≤ θ)
    (hx : 223938 / 10000000 ≤ x) (hd : d ≤ 8 * (1 - x) * θ) :
    d ≤ (782085 / 100000 : ℝ) * θ := by
  have hcoef : 8 * (1 - x) ≤ (782085 / 100000 : ℝ) := by linarith
  exact hd.trans (mul_le_mul_of_nonneg_right hcoef hθ)

/-- The paper's 7.82085 implies Theorem 1's 7.8209.
CONDITIONAL ON the supplied asymptotic sieve bound. -/
theorem theorem1_of_sieve
    (h : ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N →
      ∃ x : ℝ, 223938 / 10000000 ≤ x ∧ (D N : ℝ) ≤ 8 * (1 - x) * Θ N) :
    GoldbachUpper (78209 / 10000 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨N₀, fun N hEven hN => ?_⟩
  obtain ⟨x, hx, hd⟩ := hN₀ N hEven hN
  have hp := printed_constant_of_bound (Θ_nonneg N) hx hd
  exact hp.trans (mul_le_mul_of_nonneg_right (by norm_num) (Θ_nonneg N))

/-- Concrete instance with positive normalizer and equality at the input bound. -/
theorem printed_constant_instance :
    8 * (1 - (223938 / 10000000 : ℝ)) * 1 ≤ (782085 / 100000 : ℝ) * 1 :=
  printed_constant_of_bound (by norm_num) le_rfl le_rfl

/-- A nonzero two dimensional instance for the matrix comparison theorem. -/
theorem comparison_instance :
    ∀ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i ≤ (![2, 3] : Fin 2 → ℝ) i := by
  apply section7_comparison (0 : Matrix (Fin 2) (Fin 2) ℝ) 1 ![1, 2] ![2, 3] ![1, 2]
  · intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num
  · simp
  · intro i; fin_cases i <;> norm_num
  · simp

end LeanLab.ChenDoubleSieve.Wu04Numerics

#print axioms LeanLab.ChenDoubleSieve.Wu04Numerics.mulVec_mono
#print axioms LeanLab.ChenDoubleSieve.Wu04Numerics.section7_comparison
#print axioms LeanLab.ChenDoubleSieve.Wu04Numerics.printed_constant_slack
#print axioms LeanLab.ChenDoubleSieve.Wu04Numerics.printed_constant_of_bound
#print axioms LeanLab.ChenDoubleSieve.Wu04Numerics.theorem1_of_sieve
#print axioms LeanLab.ChenDoubleSieve.Wu04Numerics.printed_constant_instance
#print axioms LeanLab.ChenDoubleSieve.Wu04Numerics.comparison_instance
