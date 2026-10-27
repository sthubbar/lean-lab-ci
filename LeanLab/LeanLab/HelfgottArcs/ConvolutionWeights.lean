/-
Endpoint and zero extension versions of the smoothing convolution identity.
Source: https://arxiv.org/abs/1205.5252v4, page 31 equations 4.2 and 4.3.
AI wrote this Lean code for CODEX task62. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.WeightBounds

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real Filter

/-- The zero extensions make the convolution identity valid on the whole real line. -/
theorem eta2_eq_mconv_all (t : ℝ) : mconv eta1 eta1 t = eta2 t := by
  by_cases ht : 0 < t
  · exact eta2_eq_mconv t ht
  · unfold eta2 mconv
    rw [if_neg ht]
    have hn : t ≤ 0 := le_of_not_gt ht
    calc (∫ y in Ioi (0 : ℝ), eta1 y * eta1 (t / y) / y)
        = ∫ _y in Ioi (0 : ℝ), (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y hy
          have hdiv : t / y ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn hy.le
          have hnot : t / y ∉ Icc (1 / 2 : ℝ) 1 := by
            intro h
            linarith [h.1]
          have hz : eta1 (t / y) = 0 := indicator_of_notMem hnot _
          change eta1 y * eta1 (t / y) / y = 0
          rw [hz, mul_zero, zero_div]
      _ = 0 := by simp

/-- Equation 4.2 with the interval open at 1/2 exactly as printed in equation 4.3. -/
theorem eta2_eq_mconv_Ioc (t : ℝ) :
    mconv ((Ioc (1 / 2 : ℝ) 1).indicator (fun _ => (2 : ℝ)))
      ((Ioc (1 / 2 : ℝ) 1).indicator (fun _ => (2 : ℝ))) t = eta2 t := by
  let f : ℝ → ℝ := (Ioc (1 / 2 : ℝ) 1).indicator (fun _ => 2)
  have ef : ∀ s : ℝ, s ≠ 1 / 2 → f s = eta1 s := by
    intro s hs
    by_cases hm : s ∈ Ioc (1 / 2 : ℝ) 1
    · have hc : s ∈ Icc (1 / 2 : ℝ) 1 := ⟨hm.1.le, hm.2⟩
      dsimp [f, eta1]
      rw [indicator_of_mem hm, indicator_of_mem hc]
    · have hn : s ∉ Icc (1 / 2 : ℝ) 1 := by
        intro hc
        exact hm ⟨lt_of_le_of_ne hc.1 hs.symm, hc.2⟩
      dsimp [f, eta1]
      rw [indicator_of_notMem hm, indicator_of_notMem hn]
  change mconv f f t = eta2 t
  rw [← eta2_eq_mconv_all t]
  unfold mconv
  apply setIntegral_congr_ae measurableSet_Ioi
  filter_upwards [volume.ae_ne (1 / 2 : ℝ), volume.ae_ne (2 * t)] with y hyhalf hytwo hy
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hdiv : t / y ≠ 1 / 2 := by
    intro heq
    have hmul : t = (1 / 2 : ℝ) * y := (div_eq_iff hy0).mp heq
    apply hytwo
    linarith
  change f y * f (t / y) / y = eta1 y * eta1 (t / y) / y
  rw [ef y hyhalf, ef (t / y) hdiv]

end LeanLab.HelfgottArcs
