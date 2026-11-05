import LeanLab.HardyLittlewood1923.Decomp354d

/-!
AI wrote this Lean code for CODEX task354.
P0004 pages 19 to 23 equations 2.823 and 3.121.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354c

open Real Finset
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp276c

/-- LEAF. P0004 page 19 Lemma 9 equation 2.823, proved on pages 19 to 21.
Specialize eta to one over n while retaining the original polynomial terms
sqrt q times q plus eta to minus one half. The analytic zero sum estimate
is separate from the elementary absorption into n to three quarters.
The internal cited proof uses Lemmas 4 and 7 and the zero count 2.611. -/
theorem lemma9_on_circle {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤
          C * (Real.sqrt q * ((q : ℝ) + Real.sqrt n) + angularTerm Θ n q θ) *
            Real.log ((q : ℝ) + 1) ^ A := by
  sorry

/-- P0004 page 23 equation 3.121, absorbing the polynomial modulus terms. -/
theorem polynomial_arc_factor {n q : ℕ} (hq : q ≤ Nat.sqrt n) :
    Real.sqrt q * ((q : ℝ) + Real.sqrt n) ≤ 2 * (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hqR : (q : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (by positivity) hn).mpr (by exact_mod_cast (show q ^ 2 ≤ n by simpa [pow_two] using Nat.le_sqrt.mp hq))
  have he : (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt n = (n : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hn (by norm_num : (1 / 4 : ℝ) + 1 / 2 ≠ 0)]
    norm_num
  calc
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (Real.sqrt n + Real.sqrt n) := by
      gcongr
      exact Decomp354d.sqrt_modulus_le hq
    _ = _ := by nlinarith only [he]

/-- P0004 page 23 equation 3.121.
The exact preliminary target follows from Lemma 9 and polynomial absorption.
CONDITIONAL on lemma9_on_circle. -/
theorem preliminary_arc_error {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤
          C * ((n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ) * Real.log n ^ A := by
  obtain ⟨A, C, hC, n₀, hc⟩ := lemma9_on_circle hΘ0 hΘ1 hZ
  refine ⟨A, 2 * C, by positivity, max n₀ 4, fun n hn q hq hqN p hp hpq θ hθ => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hlog0 : 0 ≤ Real.log ((q : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have hlog : Real.log ((q : ℝ) + 1) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (by have := Nat.sqrt_lt_self (by omega : 1 < n); omega : q + 1 ≤ n)
  have hterm : 0 ≤ angularTerm Θ n q θ := by
    unfold angularTerm
    have hg := angularGap_pos (by omega : 0 < n) θ
    have hl : 0 ≤ Real.log (1 / angularGap n θ + 2) :=
      Real.log_nonneg (by
        have : 0 < 1 / angularGap n θ := by positivity
        linarith)
    positivity
  have hpoly := polynomial_arc_factor hqN
  calc
    _ ≤ C * (Real.sqrt q * ((q : ℝ) + Real.sqrt n) + angularTerm Θ n q θ) *
          Real.log ((q : ℝ) + 1) ^ A := hc n hn0 q hq hqN p hp hpq θ hθ
    _ ≤ C * (2 * ((n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ)) * Real.log n ^ A := by
      apply mul_le_mul _ (pow_le_pow_left₀ hlog0 hlog A) (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      linarith
    _ = _ := by ring

#print axioms lemma9_on_circle
#print axioms polynomial_arc_factor
#print axioms preliminary_arc_error

end LeanLab.HardyLittlewood1923.Decomp354c
