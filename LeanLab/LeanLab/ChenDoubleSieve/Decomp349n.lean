import LeanLab.ChenDoubleSieve.Decomp349m

/-!
The inverse substitution for the first upper coefficient in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The inverse prime coordinate gives exactly the printed first upper integral. -/
theorem variableKernel_integral (F : ℝ → ℝ) (hF : ContinuousOn F (Ioi (0 : ℝ))) :
    (∫ t in kappa1..kappa2, variableKernel F t / t) =
      4 / exp eulerMascheroniConstant *
        ∫ u in (1 / (2 * kappa2) - 1)..(1 / (2 * kappa1) - 1), F u := by
  let g : ℝ → ℝ := fun t => 1 / (2 * t) - 1
  let g' : ℝ → ℝ := fun t => -1 / (2 * t ^ 2)
  have hkle : kappa1 ≤ kappa2 := by norm_num [kappa1, kappa2]
  have htpos : ∀ t ∈ Set.uIcc kappa1 kappa2, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hkle] at ht
    exact lt_of_lt_of_le (by norm_num [kappa1]) ht.1
  have hd : ∀ t ∈ Set.uIcc kappa1 kappa2, HasDerivAt g (g' t) t := by
    intro t ht
    have ht0 := (htpos t ht).ne'
    have h2t : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht0
    have hraw := ((hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).const_mul 2) h2t).sub_const 1
    convert hraw using 1 <;> dsimp [g, g'] <;> field_simp <;> ring
  have hdc : ContinuousOn g' (Set.uIcc kappa1 kappa2) := by
    dsimp [g']
    fun_prop (disch := intro t ht; have := htpos t ht; positivity)
  have hFi : ContinuousOn F (g '' Set.uIcc kappa1 kappa2) := hF.mono (by
    rintro u ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hkle] at ht
    have hr := variable_argument_range ht
    change 0 < 1 / (2 * t) - 1
    linarith [hr.1])
  have he := intervalIntegral.integral_comp_mul_deriv' hd hdc hFi
  calc
    _ = (-4 / exp eulerMascheroniConstant) *
        ∫ t in kappa1..kappa2, (F ∘ g) t * g' t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 := (htpos t ht).ne'
      dsimp [variableKernel, g, g']
      field_simp
      <;> ring
    _ = (-4 / exp eulerMascheroniConstant) * ∫ u in g kappa1..g kappa2, F u := by rw [he]
    _ = 4 / exp eulerMascheroniConstant * ∫ u in g kappa2..g kappa1, F u := by
      rw [intervalIntegral.integral_symm (a := g kappa1) (b := g kappa2)]
      ring
    _ = _ := rfl

/-- Coordinate one of the exact ordinary finite main term limit is supplied.
CONDITIONAL ON IsLinearSieve only. The sieve count comparison is separate. -/
theorem basic_main_one_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) :
    Tendsto (fun N : ℕ => basicMain F B N 1 / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 1)) := by
  have ht := basicMain_variable_tendsto F f h B
  rw [variableKernel_integral F h.1] at ht
  simpa [integralTerms] using ht

end LeanLab.ChenDoubleSieve.Task349
