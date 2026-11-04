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

/-
RETIRED 2026-10-31 architect PC 20261031T2333Z-383, kept as text. Two leaves of the task579 split:
`leaf_constants_exist : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∃ c H0 X0 : ℝ, 0 < c`
and `leaf_main_term_bound_exists_C (ε ε0 c H0 X0 : ℝ) : ∃ C : ℝ, ∀ H X P0 P Sg', Thm1Hyp ε H0 X0 H X P0 →
P0 * X ^ (-ε) ≤ P → P ≤ P0 → (convergence of every pair series at every m : ℕ) → ∀ m : ℕ, m ≤ X →
‖R1majPrime ε X P m - mainTermPrime E Sg' ε X m‖ ≤ C * (Sing m * X * exp (-(c * H)) + X ^ (1 - ε0))`.
The second was vacuous: its convergence hypothesis includes m = 0, where the pole series diverges,
Audit168.zero_no_limit and LeafAudit168.prime_zero_no_limit; and once m = 0 is dropped it would be
asked for every ε0 and c, which the paper never claims. The first carried no content. They are
merged below into `leaf_main_term_bound`, with ε0 and c existential as in Theorem 1.
-/

/-- LEAF arXiv:1804.05561v1 display 8.28: the major arc parameter P exists DECISION U-1614: `0 < ε < 4/9` added, Theorem 1 takes `ε` small, p. 8. The old form is false at
`ε = -1`, `DecompJ665.P_leaf_false`, and at `ε = 1`, `Audit1614.old_leaf_P_exists_large_eps_false`. -/
theorem leaf_P_exists {ε H0 X0 H X P0 : ℝ} (hε : 0 < ε) (hε' : ε < 4 / 9)
    (hHyp : Thm1Hyp ε H0 X0 H X P0) :
  ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H (Real.sqrt X) P X).Finite := by sorry

/-- LEAF arXiv:1804.05561v1 display 9.16: the singular series converges at every positive
frequency. DECISION 2026-10-31 architect PC 20261031T2333Z-383: `0 < m` added; the old form was
false at `m = 0`, LeafAudit168.prime_zero_no_limit. -/
theorem leaf_singular_series_converges (H X P : ℝ) :
  ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by sorry

/-- LEAF arXiv:1804.05561v1 display 10.25: the main term error is `O_ε(𝔖(m) X e^{-c_ε H}) +
O_ε(X^{1-ε₀})` for the actual series, with `ε₀` and `c_ε` existential as in Theorem 1.
DECISION 2026-10-31 architect PC 20261031T2333Z-383, replaces two retired leaves above. 
DECISION U-1614: `ε0 ≤ 1/4` added, a smaller `ε0` only weakens the claim for `X ≥ 1`; it discharges
`ε < 4/9` in `leaf_P_exists` without changing `assembly_221`. -/
theorem leaf_main_term_bound :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ 1 / 4 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      Thm1Hyp ε H0 X0 H X P0 →
      P0 * X ^ (-ε) ≤ P → P ≤ P0 →
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
      ∀ m : ℕ, (m : ℝ) ≤ X →
        ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
          C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by sorry

/-- Assembly theorem for P0054 page 8 display 2.21, proved directly from the leaves. Its
convergence clause asks `0 < m` since 2026-10-31, matching DecompJ281.leaf_221. -/
theorem assembly_221 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by
  obtain ⟨ε0, hε0, hle, h1⟩ := leaf_main_term_bound
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hε0'
  have hε49 : ε < 4 / 9 := by linarith
  obtain ⟨c, H0, C, X0, hc, hC⟩ := h1 ε hε hε0'
  refine ⟨c, H0, C, X0, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨P, hP1, hP2, hFin⟩ := leaf_P_exists hε hε49 hHyp
  refine ⟨P, hP1, hP2, hFin, ?_⟩
  obtain ⟨Sg', hSg1⟩ := leaf_singular_series_converges H X P
  exact ⟨Sg', hSg1, hC H X P0 P Sg' hHyp hP1 hP2 hSg1⟩

end
end LeanLab.Pintz2021.DecompJ579

#print axioms LeanLab.Pintz2021.DecompJ579.assembly_221
