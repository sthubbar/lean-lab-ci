/-
P0087 Akeno 2026 Theorem 1.2 pages 31 to 32 and Appendix 5.1 page 36.
The numerical tail uses conservative bounds, without the printed T7 to T10 enclosures.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Thm12Certified2
import LeanLab.Akeno2026.KuhnTail

namespace LeanLab.Akeno2026.Thm12Certified
open LeanLab.Akeno2026 LeanLab.Akeno2026.SieveFns LeanLab.Akeno2026.Thm12Numerics

/-- The conservative tail still gives M4 at least 0.0151 at the enclosure endpoints. -/
theorem m4_tail_margin :
    (0.0151 : ℝ) ≤ 33.5 * 0.56118 - 33.5 * 0.40943 -
      2 / 0.1635 * (0.3689 + 0.04193 + 0.00352) := by norm_num

/-- Theorem 1.2 conditional on analytic inputs only, with no numerical enclosure hypotheses. -/
theorem thm1_2_certified_tail
    (Mk : ℕ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (PwSmooth : (ℝ → ℝ) → Prop)
    (prop44 : ∀ k : ℕ, 2 ≤ k → ∀ θ s : ℝ, θ < 1 / 6 → 1 / θ < s → ∀ F : ℝ → ℝ,
      PwSmooth F → (∀ u, 0 ≤ F u) →
      (∃ ε : ℝ, 0 < ε ∧ Function.support F ⊆ Set.Icc 0 (θ - ε)) →
      0 < Mk k F θ s → AlmostAllDyadic Even (DiffForm k))
    (hPS : PwSmooth (kuhnF 9.5))
    (ωp ωm : ℝ → ℝ) (hω : IsOmegaPair ωp ωm)
    (hdecomp : Mk 4 (kuhnF 9.5) 0.1635 33.5 =
      33.5 * ωm (0.1635 * 33.5) - 33.5 * FIntegral.fint ωp -
        2 / 0.1635 * (T5kuhn 33.5 9.5 + T6Certified.T6kuhn 33.5 9.5 +
          KuhnTail.kuhnTr 7 + KuhnTail.kuhnTr 8 + KuhnTail.kuhnTr 9 + KuhnTail.kuhnTr 10)) :
    AlmostAllDyadic Even (DiffForm 4) := by
  refine prop44 4 (by norm_num) 0.1635 33.5 (by norm_num) (by norm_num) (kuhnF 9.5) hPS
    (kuhnF_nonneg 9.5) ⟨0.1635 - 1 / 9.5, by norm_num, ?_⟩ ?_
  · refine (kuhnF_support 9.5).trans ?_
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  · rw [hdecomp]
    have ho := omega_minus_bounds hω
    have hi := FIntegral.Fint_bounds hω
    have h5 := Thm12Certified80.T5_bounds_printed
    have h6 := T6Certified.T6_bounds
    have ht := KuhnTail.kuhnTail_bounds
    norm_num at ho h5 h6 hi ht ⊢
    nlinarith [ho.1, hi.2, h5.2, h6.2, ht.2]

end LeanLab.Akeno2026.Thm12Certified
