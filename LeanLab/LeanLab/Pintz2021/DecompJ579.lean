import Mathlib
import LeanLab.Pintz2021.Audit168
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.State1581
import LeanLab.Pintz2021.DecompJ281

namespace LeanLab.Pintz2021.DecompJ579

open Complex Finset Filter Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DifferenceTask53
open LeanLab.Pintz2021.DecompJ281

attribute [local instance] Classical.propDecidable

noncomputable section

/-- LEAF arXiv:1804.05561v1 display 8.28: the epsilon threshold and core constants exist -/
theorem leaf_constants_exist :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 X0 : ℝ, 0 < c := by
  use 1
  refine ⟨by norm_num, ?_⟩
  intro ε _ _
  use 1, 0, 0
  norm_num

/-- LEAF arXiv:1804.05561v1 display 8.28: the major arc parameter P exists -/
theorem leaf_P_exists {ε H0 X0 H X P0 : ℝ} (hHyp : Thm1Hyp ε H0 X0 H X P0) :
  ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H (Real.sqrt X) P X).Finite := by sorry

/-- LEAF arXiv:1804.05561v1 display 9.16: the singular series converges -/
theorem leaf_singular_series_converges (H X P : ℝ) :
  ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by sorry

/-- LEAF arXiv:1804.05561v1 display 10.25: the main term error is bounded by a constant C depending only on ε -/
theorem leaf_main_term_bound_exists_C (ε ε0 c H0 X0 : ℝ) :
  ∃ C : ℝ, ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    Thm1Hyp ε H0 X0 H X P0 →
    P0 * X ^ (-ε) ≤ P → P ≤ P0 →
    (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
    ∀ m : ℕ, (m : ℝ) ≤ X →
      ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
        C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by sorry

/-- Assembly theorem for P0054 page 8 display 2.21, proved directly from the leaves. -/
theorem assembly_221 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by
  obtain ⟨ε0, hε0, h1⟩ := leaf_constants_exist
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hε0'
  obtain ⟨c, H0, X0, hc⟩ := h1 ε hε hε0'
  obtain ⟨C, hC⟩ := leaf_main_term_bound_exists_C ε ε0 c H0 X0
  refine ⟨c, H0, C, X0, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨P, hP1, hP2, hFin⟩ := leaf_P_exists hHyp
  refine ⟨P, hP1, hP2, hFin, ?_⟩
  obtain ⟨Sg', hSg1⟩ := leaf_singular_series_converges H X P
  refine ⟨Sg', hSg1, ?_⟩
  exact hC H X P0 P Sg' hHyp hP1 hP2 hSg1

end
end LeanLab.Pintz2021.DecompJ579
