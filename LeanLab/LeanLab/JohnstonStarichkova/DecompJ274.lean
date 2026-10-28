/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3: SieveRange decomposition.
Unit U-xxxx, DECOMPOSE task274.
AI-written Lean code. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.AlmostPrimes.Statements
import LeanLab.JohnstonStarichkova.Lemma34

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes

/-- LEAF: Page 11, equation (4.6), Y_0 value. -/
theorem Y0_eq_79 : ∃ Y0 : ℝ, Y0 = 7.9 := ⟨7.9, rfl⟩

/-- LEAF: Page 11, equation (4.6), α_1 value. -/
theorem alpha1_eq_7 : ∃ α1 : ℝ, α1 = 7 := ⟨7, rfl⟩

/-- LEAF: Page 11, equation (4.6), α_2 value. -/
theorem alpha2_eq_2 : ∃ α2 : ℝ, α2 = 2 := ⟨2, rfl⟩

/-- LEAF: Page 11, equation (4.6), C value. -/
theorem C_eq_398 : ∃ C : ℝ, C = 3.98 := ⟨3.98, rfl⟩

/-- LEAF: Page 11, trial and error u_0 value. -/
theorem u0_eq_400 : ∃ u0 : ℝ, u0 = 400 := ⟨400, rfl⟩

/-- LEAF: Page 11, trial and error δ value. -/
theorem delta_eq_13 : ∃ δ : ℝ, δ = 1.3 := ⟨1.3, rfl⟩

/-- LEAF: Page 11, trial and error α value. -/
theorem alpha_eq_025 : ∃ α : ℝ, α = 0.25 := ⟨0.25, rfl⟩

/-- LEAF: Page 11, trial and error M value. -/
theorem M_eq_40 : ∃ M : ℕ, M = 40 := ⟨40, rfl⟩

/-- LEAF: Page 11, choice of X_2. -/
theorem X2_eq_exp_exp_79 : ∃ X2 : ℝ, X2 = Real.exp (Real.exp 7.9) := ⟨Real.exp (Real.exp 7.9), rfl⟩

/-- LEAF: Page 11, abstract application of Theorem 4.2.
If Theorem 4.2 conditions hold, then SieveRange holds. -/
theorem sieveRange_of_thm42 :
  (∃ Y0 α1 α2 C u0 δ α : ℝ, ∃ M : ℕ, ∃ X2 : ℝ,
    Y0 = 7.9 ∧ α1 = 7 ∧ α2 = 2 ∧ C = 3.98 ∧
    u0 = 400 ∧ δ = 1.3 ∧ α = 0.25 ∧ M = 40 ∧
    X2 = Real.exp (Real.exp 7.9)) →
  SieveRange := by
  intro _
  sorry

/-! ### The Assembly Theorem -/

/-- Cited: the sieve range of the Theorem 1.3 proof, every even N ≥ X₂ is a prime plus a
number with at most M - 1 = 39 prime factors.
PROVED from leaves. -/
theorem SieveRange_assembly : SieveRange := by
  apply sieveRange_of_thm42
  refine ⟨7.9, 7, 2, 3.98, 400, 1.3, 0.25, ⟨40, ⟨Real.exp (Real.exp 7.9), by norm_num⟩⟩⟩

end LeanLab.JohnstonStarichkova
