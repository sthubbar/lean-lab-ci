/-
P0069 Baker Harman Pintz 1997, pages 43 and 52.
The lab factor transfers continuous prefix mean squares with loss at most four.
The analytic prefix estimate remains an explicit hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.Task670WeightedMeanSquare

namespace LeanLab.BHP1997.Task670Normalization518
open Classical Complex MeasureTheory DecompC165b LowerShortC165
open scoped BigOperators

/-- P0069 page 43 displays 5.1 and 5.2 and page 52 before 5.18. The lab normalization
preserves a uniform prefix mean square estimate with absolute loss at most four. -/
theorem lower_factor_mean_square (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ a : ℕ → ℝ → ℂ, ∀ w : ℝ → ℝ,
      ∀ u v R : ℝ, u ≤ v → 0 ≤ R →
      (∀ m ∈ rightInterval ε x, Continuous (a m)) → Continuous w →
      (∀ t ∈ Set.Icc u v, 0 ≤ w t) →
      (∀ i ∈ Finset.Icc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (∫ t in u..v,
          ‖∑ m ∈ (rightInterval ε x).filter (fun m => m ≤ i), a m t‖ ^ 2 * w t) ≤ R) →
      (∫ t in u..v, ‖∑ m ∈ rightInterval ε x,
        (lowerFactor ω ε x m : ℂ) * a m t‖ ^ 2 * w t) ≤ 4 * R := by
  obtain ⟨X, hX⟩ := Decomp514a.leaf_factor_variation ω hω hz hε hε8
  refine ⟨max X 1, fun x hx a w u v R huv hR ha hw hw0 hprefix => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  let L : ℕ := ⌊x ^ (11 / 20 + ε)⌋₊
  let U : ℕ := ⌊2 * x ^ (11 / 20 + ε)⌋₊
  have hY : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hLU : L ≤ U := Nat.floor_mono (by linarith)
  have hs : ∀ m ∈ rightInterval ε x, L ≤ m ∧ m ≤ U := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hm
    exact ⟨h1.le, h2⟩
  have h := Task670WeightedMeanSquare.abel_weighted_mean_square (rightInterval ε x) hLU hs
    (fun m => (lowerFactor ω ε x m : ℂ)) a w huv ha hw hw0 hprefix
  have he : ‖(lowerFactor ω ε x U : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lowerFactor_nonneg _ _ _ _)]
    exact lowerFactor_le_one _ _ _ _
  have hv : (∑ i ∈ Finset.Ico L U,
      ‖(lowerFactor ω ε x (i + 1) : ℂ) - (lowerFactor ω ε x i : ℂ)‖) ≤ 1 := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hX x hxX
  have hv0 : 0 ≤ ∑ i ∈ Finset.Ico L U,
      ‖(lowerFactor ω ε x (i + 1) : ℂ) - (lowerFactor ω ε x i : ℂ)‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hcost : (‖(lowerFactor ω ε x U : ℂ)‖ + ∑ i ∈ Finset.Ico L U,
      ‖(lowerFactor ω ε x (i + 1) : ℂ) - (lowerFactor ω ε x i : ℂ)‖) ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (lowerFactor ω ε x U : ℂ)]
  exact h.trans (mul_le_mul_of_nonneg_right hcost hR)

end LeanLab.BHP1997.Task670Normalization518
