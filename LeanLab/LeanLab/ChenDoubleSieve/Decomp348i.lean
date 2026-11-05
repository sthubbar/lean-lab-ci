import LeanLab.ChenDoubleSieve.Decomp348h

/-!
Exact assemblies and unrestricted limit bridges for Wu 2004 equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- An unrestricted F4 limit implies the original prime sum limit.
CONDITIONAL ON IsLinearSieve and the explicitly stated unrestricted limit. -/
theorem lowerSum4_of_full (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B)
    (hfull : Tendsto (fullSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f))) :
    Tendsto (lowerSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f)) := by
  have hd : Tendsto (fun N => dist (fullSum4 f B N) (lowerSum4 f B N)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K, hK⟩ := lowerSum4_coprimality F f h B hB (ε / 2) (by positivity)
    refine ⟨K, ?_⟩
    intro N hN
    simpa only [Real.dist_eq, sub_zero, abs_abs] using
      (hK N hN).trans_lt (by linarith : ε / 2 < ε)
  exact hfull.congr_dist (tendsto_inf_left hd)

/-- An unrestricted F5 limit implies the original prime sum limit.
CONDITIONAL ON IsLinearSieve and the explicitly stated unrestricted limit. -/
theorem lowerSum5_of_full (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B)
    (hfull : Tendsto (fullSum5 f B) evenAtTop (𝓝 (lowerIntegral5 f))) :
    Tendsto (lowerSum5 f B) evenAtTop (𝓝 (lowerIntegral5 f)) := by
  have hd : Tendsto (fun N => dist (fullSum5 f B N) (lowerSum5 f B N)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K, hK⟩ := lowerSum5_coprimality F f h B hB (ε / 2) (by positivity)
    refine ⟨K, ?_⟩
    intro N hN
    simpa only [Real.dist_eq, sub_zero, abs_abs] using
      (hK N hN).trans_lt (by linarith : ε / 2 < ε)
  exact hfull.congr_dist (tendsto_inf_left hd)

/-- The original positive estimate type follows from the three exact new supplies.
OPEN through the six strictly smaller analytic leaves. -/
theorem positive_estimates_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 ∧
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 ∧
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  intro ε hε
  obtain ⟨M0, h0⟩ := lower_F0_supplied F f ω h hω ε hε
  obtain ⟨M4, h4⟩ := lower_F4_supplied F f ω h hω ε hε
  obtain ⟨M5, h5⟩ := lower_F5_supplied F f ω h hω ε hε
  refine ⟨max M0 (max M4 M5), ?_⟩
  intro N hEven hN
  exact ⟨h0 N hEven (by omega), h4 N hEven (by omega), h5 N hEven (by omega)⟩

end LeanLab.ChenDoubleSieve.Task348
