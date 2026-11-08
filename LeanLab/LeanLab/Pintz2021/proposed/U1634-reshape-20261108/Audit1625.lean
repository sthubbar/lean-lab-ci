/-
Unit U-1625, run 20261106T0803Z-25677. Instances for the repaired `DecompJ281.leaf_221` and
`DecompJ281.leaf_truncation_error`: the new hypotheses are met together at level one.

AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Pintz2021.DecompJ281
import LeanLab.Pintz2021.DecompJ665

namespace LeanLab.Pintz2021.Audit1625

open Filter Topology
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DecompJ281 LeanLab.Pintz2021.DecompJ665

/-- The repaired range of `leaf_221` is met above every threshold, at `P₀ = P = 1`. -/
theorem leaf_221_range_instance {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 4 / 9) (H0 X0 : ℝ) :
    ∃ H X P0 P : ℝ, Thm1Hyp_v2 ε H0 X0 H X P0 ∧ 1 ≤ P ∧ P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 := by
  obtain ⟨H, X, hHyp, hX, -⟩ := level_one_tail_hyp hε hε4 H0 X0
  have hx : X ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  exact ⟨H, X, 1, 1, hHyp, le_rfl, by simpa using hx, le_rfl⟩

/-- Every hypothesis of the repaired `leaf_truncation_error` holds at once, above every threshold,
at `P₀ = P = 1`, `U = 2` and a positive even `m`, with the actual series of level one. -/
theorem leaf_truncation_range_instance {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 4 / 9) (H0 X0 : ℝ) :
    ∃ (H X P0 P U : ℝ) (Sg' : ExcPair → ExcPair → ℕ → ℂ) (m : ℕ),
      Thm1Hyp_v2 ε H0 X0 H X P0 ∧ 1 ≤ P ∧ P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
      (excSet H (Real.sqrt X) P X).Finite ∧
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
        Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) ∧
      X / 4 ≤ m ∧ (m : ℝ) ≤ X / 2 ∧ 2 ≤ U ∧ U ≤ Real.sqrt X := by
  obtain ⟨H, X, hHyp, hX, hpow⟩ := level_one_tail_hyp hε hε4 H0 X0
  obtain ⟨m, -, -, hlo, hhi, -⟩ := positive_even_kernel_in_range hX hpow
  obtain ⟨Sg, hSg⟩ := level_one_series_converges H X 1 le_rfl
  have hx : X ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hU : (2 : ℝ) ≤ Real.sqrt X := Real.le_sqrt' (by norm_num) |>.mpr (by linarith)
  exact ⟨H, X, 1, 1, 2, Sg, m, hHyp, le_rfl, by simpa using hx, le_rfl,
    excSet_finite _ _ _ _, hSg, hlo, hhi, le_rfl, hU⟩

end LeanLab.Pintz2021.Audit1625

#print axioms LeanLab.Pintz2021.Audit1625.leaf_221_range_instance
#print axioms LeanLab.Pintz2021.Audit1625.leaf_truncation_range_instance
