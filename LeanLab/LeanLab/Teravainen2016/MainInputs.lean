/-
P0076 analytic leaves for the four main theorem assemblies.
Every declaration in this file is unresolved and CONDITIONAL.
No leaf is certified by its cited source or by compilation with sorryAx.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.BinaryBridge
import LeanLab.Teravainen2016.ProgressionLifting
import LeanLab.Teravainen2016.DyadicApproximation

namespace LeanLab.Teravainen2016

/-- LEAF. Page 6, the cutoff existence quoted from Matomaki and Shao Lemma 3.1.
CONDITIONAL ON that published cutoff construction. -/
theorem paper_smooth_cutoff_input : ChiExists := by sorry

/-- LEAF. Page 9, Proposition 3.2, with the bounded shift reading in Transference.lean.
CONDITIONAL ON the weighted prime distribution estimate proved in Sections 5 through 10. -/
theorem paper_weighted_prime_input : Prop32 := by sorry

/-- LEAF. Page 11, the half interval refinement of Proposition 3.2.
CONDITIONAL ON this weighted prime distribution refinement.
This refinement is not the printed dyadic Proposition 3.2. -/
theorem paper_half_interval_input : Prop32Half := by sorry

/-- LEAF. Page 9, Proposition 3.3, and pages 13 to 17, its restriction argument.
CONDITIONAL ON the reconstructed bounded shift and changed scale restriction input.
This avoids assuming unrestricted uniformity in all integer shifts. -/
theorem paper_cross_scale_restriction_input : Prop33Cross := by sorry

/-- LEAF. Pages 9 to 12, the ternary deduction in Remark 3.6.
CONDITIONAL ON the cited Matomaki and Shao Theorem 2.3. -/
theorem paper_ternary_transference_input : MSThm23 := by sorry

/-- LEAF. Page 17, the Section 4 dense model and Green Tao transference argument.
CONDITIONAL ON that analytic modular progression output.
This is its modular output before the elementary lifting step. -/
theorem paper_dense_modular_progressions_input (A : Set ℕ)
    (hA : A ⊆ PStar) (hδ : PosUpperDensityIn A PStar) :
    ∀ X : ℕ, ∃ N a b c : ℕ, X ≤ N ∧
      a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
      N < 3 * a ∧ 3 * a < 2 * N ∧
      N < 3 * b ∧ 3 * b < 2 * N ∧
      N < 3 * c ∧ 3 * c < 2 * N ∧
      a ≠ b ∧ (a : ZMod N) + c = 2 * b := by sorry

/-- LEAF. Pages 44 to 47, the Section 11 prime approximation estimate.
CONDITIONAL ON that prime approximation estimate.
The positive frequency and small positive exponent reading precedes display 11.1. -/
theorem paper_dyadic_approximation_input (ξ : ℝ) (hξ : Irrational ξ) (hξ0 : 0 < ξ)
    (κ θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 80) :
    ∀ X : ℕ, ∃ N p : ℕ, max 1 X ≤ N ∧ N ≤ p ∧ p ≤ 2 * N ∧
      InP p ∧ distInt (ξ * p + κ) ≤ (N : ℝ) ^ (-θ) / 2 := by sorry

end LeanLab.Teravainen2016
