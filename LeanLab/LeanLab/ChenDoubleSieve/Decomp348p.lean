import LeanLab.ChenDoubleSieve.Decomp348o

/-!
Exact lower sieve supplies using the proved density normalization.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39.
Five analytic leaves remain: three raw sieve bounds and two prime sum limits.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348.Supplied
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The finite F0 main term limit uses the proved density normalization.
CONDITIONAL ON IsLinearSieve only. -/
theorem main0_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) :
    Tendsto (fun N => main0 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 0)) := by
  have hc : ContinuousAt f (6 : ℝ) := h.2.1.continuousAt (Ioi_mem_nhds (by norm_num))
  have hf : Tendsto (fun N => f (lowerLevel B N 1)) evenAtTop (𝓝 (f 6)) :=
    hc.tendsto.comp (tendsto_inf_left (lowerLevel_one_tendsto B))
  have ht := scaledDensity_supplied.mul hf
  have ht' : Tendsto (fun N => scaledDensity N * f (lowerLevel B N 1))
      evenAtTop (𝓝 (integralTerms F f ω 0)) := by
    convert ht using 1
    change 𝓝 (2 * f (1 / (2 * kappa1)) / (kappa1 * exp eulerMascheroniConstant)) = _
    congr 1
    rw [show (1 / (2 * kappa1) : ℝ) = 6 by norm_num [kappa1]]
    ring
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main0_ratio f B hN).symm


/-- The finite F4 main term limit uses the proved density normalization.
OPEN through the corresponding prime sum limit. -/
theorem main4_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N => main4 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 4)) := by
  have ht := scaledDensity_supplied.mul (lowerSum4_tendsto F f h B hB)
  have ht' : Tendsto (fun N => scaledDensity N * lowerSum4 f B N)
      evenAtTop (𝓝 (integralTerms F f ω 4)) := by
    convert ht using 1
    change 𝓝 (2 / (kappa1 * exp eulerMascheroniConstant) * lowerIntegral4 f) = _
    rfl
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main4_ratio f B hN).symm


/-- The finite F5 main term limit uses the proved density normalization.
OPEN through the corresponding prime sum limit. -/
theorem main5_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N => main5 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 5)) := by
  have ht := scaledDensity_supplied.mul (lowerSum5_tendsto F f h B hB)
  have ht' : Tendsto (fun N => scaledDensity N * lowerSum5 f B N)
      evenAtTop (𝓝 (integralTerms F f ω 5)) := by
    convert ht using 1
    change 𝓝 (2 / (kappa1 * exp eulerMascheroniConstant) * lowerIntegral5 f) = _
    rfl
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main5_ratio f B hN).symm


/-- The exact original F0 conclusion uses the proved density supply.
OPEN through the remaining raw sieve and prime sum leaves only. -/
theorem lower_F0 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0  := by
  exact lower_of_main _ _ (main0 f) (main0_lower F f h)
    (fun B hB => main0_tendsto F f ω h B)

/-- The exact original F4 conclusion uses the proved density supply.
OPEN through the remaining raw sieve and prime sum leaves only. -/
theorem lower_F4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4  := by
  exact lower_of_main _ _ (main4 f) (main4_lower F f h)
    (fun B hB => main4_tendsto F f ω h B hB)

/-- The exact original F5 conclusion uses the proved density supply.
OPEN through the remaining raw sieve and prime sum leaves only. -/
theorem lower_F5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5  := by
  exact lower_of_main _ _ (main5 f) (main5_lower F f h)
    (fun B hB => main5_tendsto F f ω h B hB)

/-- The exact combined lower estimate uses five remaining analytic leaves. -/
theorem positive_estimates_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 ∧
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 ∧
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  intro ε hε
  obtain ⟨M₀, h₀⟩ := lower_F0 F f ω h hω ε hε
  obtain ⟨M₄, h₄⟩ := lower_F4 F f ω h hω ε hε
  obtain ⟨M₅, h₅⟩ := lower_F5 F f ω h hω ε hε
  refine ⟨max M₀ (max M₄ M₅), ?_⟩
  intro N hEven hN
  exact ⟨h₀ N hEven (by omega), h₄ N hEven (by omega), h₅ N hEven (by omega)⟩


end LeanLab.ChenDoubleSieve.Task348.Supplied
