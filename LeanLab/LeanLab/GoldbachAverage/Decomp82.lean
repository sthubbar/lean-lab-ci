import LeanLab.GoldbachAverage.GallagherConsequence82

/-!
Decomposition of P0051 Corollary 2, arXiv 2110.14250v2 pages 19 and 20.
The final assembly has exactly the cited proposition. Its cited leaves remain explicit.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp82
open Complex Finset MeasureTheory
open GSInputs

/-- LEAF. P0051 page 19 eq. 82. External input: Grosswald 1965,
Sur l'ordre de grandeur des differences psi x minus x et pi x minus li x.
This leaf asserts the published bound and remains cited. -/
theorem grosswald_82 : GrosswaldPsiTheta := by
  sorry

/-- LEAF. P0051 page 20 eq. 84. External input: BHMS19 Lemma 8,
Bhowmik, Halupczok, Matsumoto and Suzuki, Mathematika 65, q equal to one.
This leaf asserts the published dyadic variance bound and remains cited. -/
theorem bhms_84 : BHMSShortIntervalVariance := by
  sorry

/-- LEAF. P0051 page 20 eqs. 83 to 85. The edge bound and dyadic summation
extend the cited short interval estimate to the full interval from zero. -/
theorem full_variance_85 (hG : GrosswaldPsiTheta)
    (hD : BHMSShortIntervalVariance) : GSFullVariance := by
  exact full_variance_of_inputs hG hD

/-- LEAF. P0051 page 4 Theorem 2 eq. 19, proved on pages 8 to 10.
Gallagher's lemma bounds the local Fourier mean square by H and J. -/
theorem gallagher_19 : GSGallagherVarianceBound := by
  sorry

/-- LEAF. P0051 page 20, last line of the proof of Theorem 6.
Insert eqs. 83 and 85 in Theorem 2 and sum the geometric tails and Fourier layers.
The existing BHMSTheorem6E records the norm consequence of the majorant bound. -/
theorem error_from_variances (hG : GrosswaldPsiTheta) (hJ : GSFullVariance)
    (hW : GSGallagherVarianceBound) : GSCor2.BHMSTheorem6E := by
  exact error_of_variance_inputs hG hJ hW

/-- Corollary 2 eq. 34, page 6, assembled from its leaves with no sorry here.
CONDITIONAL ON the cited analytic leaves. This is not an unconditional proof. -/
theorem gs_corollary2_assembled : 1 / 2 ≤ Theta → Theta < 3 / 4 → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ,
    N₀ ≤ N → ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2
      + 2 * zeroSum (fun ρ => if 1 / 2 ≤ ρ.re then (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) else 0)‖
      ≤ ε * (N : ℝ) ^ ((3 : ℝ) / 2) := by
  exact GSCor2.gs_corollary2_of_bhms
    (error_from_variances grosswald_82 (full_variance_85 grosswald_82 bhms_84) gallagher_19)

example : type_of% gs_corollary2 := gs_corollary2_assembled

end LeanLab.GoldbachAverage.Decomp82
