import Mathlib
noncomputable section
open Real MeasureTheory intervalIntegral
/-!
Elementary integral calculations for Wu 2004 page 41 equations 10.9 and 10.11.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ChenDoubleSieve.Task693
/-- The inner partial-summation integral in Wu 2004 equations 10.9 and 10.11. -/
theorem inner_switching_integral {t a : ℝ} (ht : 0 < t) (_ht1 : t < 1)
    (ha : 0 < a) (hab : a ≤ (1 - t) / 2) :
    (∫ u in a..((1 - t) / 2), 1 / (t * u * (1 - t - u))) =
      log ((1 - t - a) / a) / (t * (1 - t)) := by
  have ht0 : t ≠ 0 := ht.ne'
  have ht10 : 1 - t ≠ 0 := by linarith
  have hpos : ∀ u ∈ Set.uIcc a ((1 - t) / 2), 0 < u ∧ 0 < 1 - t - u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    constructor <;> linarith [hu.1, hu.2]
  have hd : ∀ u ∈ Set.uIcc a ((1 - t) / 2),
      HasDerivAt (fun v : ℝ => (log v - log (1 - t - v)) / (t * (1 - t)))
        (1 / (t * u * (1 - t - u))) u := by
    intro u hu
    have h1 := (hpos u hu).1.ne'
    have h2 := (hpos u hu).2.ne'
    have h := ((hasDerivAt_log h1).sub
      (((hasDerivAt_const u (1 - t)).sub (hasDerivAt_id u)).log h2)).div_const (t * (1 - t))
    convert h using 1
    · rfl
    · dsimp
      field_simp [h1, h2, ht0, ht10]
      ring
  have hi : IntervalIntegrable (fun u : ℝ => 1 / (t * u * (1 - t - u))) volume a ((1 - t) / 2) := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := intro u hu; exact mul_ne_zero (mul_ne_zero ht0 (hpos u hu).1.ne') (hpos u hu).2.ne')
  rw [integral_eq_sub_of_hasDerivAt hd hi]
  have hmid : 1 - t - (1 - t) / 2 = (1 - t) / 2 := by ring
  rw [hmid, sub_self, zero_div, zero_sub, log_div (by linarith : 1 - t - a ≠ 0) ha.ne']
  ring

/-- The reciprocal substitution in Wu 2004 page 41 equation 10.9. -/
theorem outer_switching_integral {σ : ℝ} (hs : 0 < σ) (hs3 : σ ≤ 1 / 3) :
    (∫ t in σ..(1 / 3 : ℝ), log (1 / t - 2) / (t * (1 - t))) =
      ∫ u in (2 : ℝ)..(1 / σ - 1), log (u - 1) / u := by
  let g : ℝ → ℝ := fun t => 1 / t - 1
  let gp : ℝ → ℝ := fun t => -1 / t ^ 2
  have hpos : ∀ t ∈ Set.uIcc σ (1 / 3 : ℝ), 0 < t ∧ t < 1 := by
    intro t ht
    rw [Set.uIcc_of_le hs3] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hg2 : ∀ t ∈ Set.uIcc σ (1 / 3 : ℝ), 2 ≤ g t := by
    intro t ht
    rw [Set.uIcc_of_le hs3] at ht
    dsimp [g]
    have ht0 := (hpos t ((Set.uIcc_of_le hs3).symm ▸ ht)).1
    have hi : (3 : ℝ) ≤ 1 / t := (le_div_iff₀ ht0).mpr (by linarith [ht.2])
    linarith
  have hd : ∀ t ∈ Set.uIcc σ (1 / 3 : ℝ), HasDerivAt g (gp t) t := by
    intro t ht
    have ht0 := (hpos t ht).1.ne'
    have h := ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht0).sub_const 1
    convert h using 1 <;> dsimp [g, gp] <;> field_simp <;> ring
  have hdc : ContinuousOn gp (Set.uIcc σ (1 / 3 : ℝ)) := by
    dsimp [gp]
    fun_prop (disch := intro t ht; exact pow_ne_zero 2 (hpos t ht).1.ne')
  have hc : ContinuousOn (fun u : ℝ => log (u - 1) / u)
      (g '' Set.uIcc σ (1 / 3 : ℝ)) := by
    refine ((continuousOn_id.sub continuousOn_const).log ?_).div continuousOn_id ?_
    · rintro u ⟨t, ht, rfl⟩
      change g t - 1 ≠ 0
      have := hg2 t ht
      linarith
    · rintro u ⟨t, ht, rfl⟩
      have := hg2 t ht
      linarith
  have hsub := integral_comp_mul_deriv' hd hdc hc
  dsimp only [Function.comp_def] at hsub
  calc (∫ t in σ..(1 / 3 : ℝ), log (1 / t - 2) / (t * (1 - t)))
      = -(∫ t in σ..(1 / 3 : ℝ), (log (g t - 1) / g t) * gp t) := by
        rw [← intervalIntegral.integral_neg]
        apply integral_congr
        intro t ht
        have ht0 := (hpos t ht).1.ne'
        have ht1 : 1 - t ≠ 0 := by linarith [(hpos t ht).2]
        have hg0 : 1 / t - 1 ≠ 0 := by have := hg2 t ht; dsimp [g] at this; linarith
        dsimp [g, gp]
        have he : 1 / t - 1 - 1 = 1 / t - 2 := by ring
        rw [he]
        field_simp [ht0, ht1, hg0]
        <;> ring
    _ = -(∫ u in g σ..g (1 / 3), log (u - 1) / u) := by rw [hsub]
    _ = _ := by
      rw [integral_symm]
      norm_num [g]

/-- The evaluated triangular double integral in Wu 2004 page 41 equation 10.9. -/
theorem triangle_switching_integral {σ : ℝ} (hs : 0 < σ) (hs3 : σ ≤ 1 / 3) :
    (∫ t in σ..(1 / 3 : ℝ), ∫ u in t..((1 - t) / 2), 1 / (t * u * (1 - t - u))) =
      ∫ u in (2 : ℝ)..(1 / σ - 1), log (u - 1) / u := by
  rw [← outer_switching_integral hs hs3]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hs3] at ht
  have ht0 : 0 < t := hs.trans_le ht.1
  dsimp only
  rw [inner_switching_integral ht0 (by linarith [ht.2]) ht0 (by linarith [ht.2])]
  congr 2
  field_simp
  ring

end LeanLab.ChenDoubleSieve.Task693
