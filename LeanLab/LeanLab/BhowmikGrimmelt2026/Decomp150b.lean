/-
Theorem 5.1, P0029 pages 17 to 20.
OPEN leaves for Jules. Both cases retain the cited Gallagher inputs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerSaving)

/-- LEAF. Pages 17 to 20, the no Siegel zero case of the major arc argument.
Use 5.2, 5.3 and Proposition 5.2 part one, then the minor arc second moment.
Cited inputs: Montgomery and Vaughan 1975 Lemma 5.5 and Gallagher 1970.
OPEN. Half of the small power absorbs the fixed logarithmic losses. -/
theorem mv_no_siegel150 (h52 : Prop52) (hGallagher : GallagherStandard) :
    ∃ ϑ₀ : ℝ, 0 < ϑ₀ ∧ ∀ ϑ : ℝ, 0 < ϑ → ϑ < ϑ₀ → ϑ < 1 / 5 →
      ∃ C X₀ : ℝ, ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
        (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
          SiegelZero (X ^ ϑ) r χ β) →
        (Edy X : ℝ) ≤ C * X ^ (1 - ϑ / 2) := by
  sorry

/-- LEAF. Page 20 display 5.4 and the paragraph after it, the Siegel zero case.
The factor one minus beta times log N occurs in both the main term lower bound
and Proposition 5.2 part two. Cited inputs: Montgomery and Vaughan 1975,
and Gallagher 1970. OPEN. A uniform lower bound including proper prime powers
is required before the exceptional set count. -/
theorem mv_siegel150 (h52 : Prop52) (hGallagher : GallagherStandard) :
    ∃ ϑ₀ : ℝ, 0 < ϑ₀ ∧ ∀ ϑ : ℝ, 0 < ϑ → ϑ < ϑ₀ → ϑ < 1 / 5 →
      ∃ C X₀ : ℝ, ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
        (∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
          SiegelZero (X ^ ϑ) r χ β) →
        (Edy X : ℝ) ≤ C * X ^ (1 - ϑ / 2) := by
  sorry

/-- Exactly the sealed PowerSaving proposition of theorem51.
CONDITIONAL on the two OPEN leaves and the cited Gallagher inputs. -/
theorem theorem51_decomposed150 : PowerSaving := by
  classical
  obtain ⟨u, hu, hno⟩ := mv_no_siegel150 prop52 gallagherStandard
  obtain ⟨v, hv, hyes⟩ := mv_siegel150 prop52 gallagherStandard
  let ϑ : ℝ := min (min u v) (1 / 5) / 2
  have hϑ : 0 < ϑ := by dsimp [ϑ]; positivity
  have hϑu : ϑ < u := by
    have := min_le_left (min u v) (1 / 5 : ℝ)
    have := min_le_left u v
    dsimp [ϑ] at *
    linarith
  have hϑv : ϑ < v := by
    have := min_le_left (min u v) (1 / 5 : ℝ)
    have := min_le_right u v
    dsimp [ϑ] at *
    linarith
  have hϑsmall : ϑ < 1 / 5 := by
    have := min_le_right (min u v) (1 / 5 : ℝ)
    dsimp [ϑ] at *
    linarith
  obtain ⟨C₁, X₁, h₁⟩ := hno ϑ hϑ hϑu hϑsmall
  obtain ⟨C₂, X₂, h₂⟩ := hyes ϑ hϑ hϑv hϑsmall
  refine ⟨ϑ / 2, by positivity, ?_⟩
  apply powerBound_of_dyadic_half (X₀ := max 2 (max X₁ X₂))
    (C := max C₁ C₂) (by linarith)
  intro X hX
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX₁ : X₁ ≤ X := (le_max_left X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hX₂ : X₂ ≤ X := (le_max_right X₁ X₂).trans ((le_max_right _ _).trans hX)
  by_cases hz : ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      SiegelZero (X ^ ϑ) r χ β
  · exact (h₂ X hX2 hX₂ hz).trans
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (Real.rpow_nonneg (by linarith : 0 ≤ X) _))
  · exact (h₁ X hX2 hX₁ hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (Real.rpow_nonneg (by linarith : 0 ≤ X) _))

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.mv_no_siegel150
#print axioms LeanLab.BhowmikGrimmelt2026.mv_siegel150
#print axioms LeanLab.BhowmikGrimmelt2026.theorem51_decomposed150
