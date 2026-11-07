/-
Uniform minor family bounds from the complete discrete multiplier.
Source: P0029 page 27 display 7.8.
The logarithm power is nine. The printed power five remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.UniformMinorWeight451
import LeanLab.BhowmikGrimmelt2026.Decomp328b

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The two minor power budget formats are identical at every positive length. -/
theorem minor_budget_identity451 {x : ℝ} (hx : 0 < x) (R : ℝ) :
    (x ^ 2 / R + x ^ (8 / 5 : ℝ)) * x =
      (R⁻¹ + x ^ (-(2 / 5) : ℝ)) * x ^ 3 := by
  have hp : x ^ (8 / 5 : ℝ) * x = x ^ (-(2 / 5) : ℝ) * x ^ 3 := by
    have h1 := Real.rpow_add hx (8 / 5 : ℝ) 1
    have h2 := Real.rpow_add hx (-(2 / 5) : ℝ) 3
    norm_num at h1 h2
    exact h1.symm.trans h2
  calc
    _ = x ^ 2 / R * x + x ^ (8 / 5 : ℝ) * x := by ring
    _ = x ^ 2 / R * x + x ^ (-(2 / 5) : ℝ) * x ^ 3 := by rw [hp]
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- The weighted minor family has logarithm power nine uniformly in all allowed eta.
There is no additive rational tail remainder. This does not prove power five. -/
theorem minor_weighted_log9_uniform451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 9 := by
  classical
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  obtain ⟨D, hD, hd⟩ := bRhat_uniform451 hG
  refine ⟨192 * (48600 : ℝ) ^ 2 * D ^ 2 * (L : ℝ) ^ 4, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  let R : ℝ := (X : ℝ) ^ ϑ
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  have hT (q : ℕ) (hq : q ∈ Finset.Icc 1 ⌊R⌋₊) : 0 < η * X * q / R := by
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    positivity
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else
    -bRhat G R (fun q => η * X * q / R) α
  let U : ℝ := (L : ℝ) *
    (48600 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 4)
  have hW : Measurable W := measurable_const.ite (measurableSet_majorArc84 X R)
    ((continuous_bRhat hG.supp hG.even R _ hT).neg.measurable)
  have hWB (α : ℝ) : ‖W α‖ ≤ D := by
    by_cases hm : MajorArc X R α
    · simp only [W, if_pos hm, norm_zero]
      exact hD.le
    · simpa [W, hm] using hd X R η hR1 hη hscale α
  have hsup (n : ℕ) (hn : n ≤ X) (α : ℝ) (hne : W α ≠ 0) : ‖Sphi ϕ n α‖ ≤ U := by
    have hm : ¬ MajorArc X R α := by
      intro hh
      exact hne (by simp [W, hh])
    exact Sphi_minor261 hϕ hL hX hR1 hRX hn hm
  have hfam := supported_family_sharp261 hϕ hL hX hW hD.le
    (by dsimp [U]; positivity : 0 ≤ U) hWB hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) =
        minorWeighted328 ϕ G X N ϑ η := by
    rw [minorWeighted_eq_integral328 hG ϕ hX N ϑ hη, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X R α <;> simp [W, Set.indicator, R, hm] <;> ring
  have hA2 : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRp.le]
  have hD2 : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  have hsq : ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 ≤
      2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA2, ← hD2]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  simp_rw [heq] at hfam
  calc
    _ ≤ 96 * D ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := hfam
    _ = 96 * (48600 : ℝ) ^ 2 * D ^ 2 * (L : ℝ) ^ 4 *
        ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 * X * Real.log X ^ 9 := by
      dsimp [U]
      ring
    _ ≤ 96 * (48600 : ℝ) ^ 2 * D ^ 2 * (L : ℝ) ^ 4 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 9 := by gcongr
    _ = (192 * (48600 : ℝ) ^ 2 * D ^ 2 * (L : ℝ) ^ 4) *
        (((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) * X) * Real.log X ^ 9 := by ring
    _ = _ := by rw [minor_budget_identity451 hXp R]; dsimp [R]; ring

/-- The full actual minor family has logarithm power nine with no rational tail remainder.
The printed logarithm power five estimate remains OPEN. -/
theorem minor_family_log9_uniform451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 9 := by
  obtain ⟨C₁, hC₁, h₁⟩ := minor_bare_log9_328 hϕ ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := minor_weighted_log9_uniform451 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hb := h₁ X hX
  have hw := h₂ X hX η hη hη1 hscale
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have heq : C₁ * ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * X * Real.log X ^ 9 =
      C₁ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 9 := by
    calc
      _ = C₁ * (((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * X) * Real.log X ^ 9 := by ring
      _ = _ := by rw [minor_budget_identity451 hXp ((X : ℝ) ^ ϑ)]; ring
  rw [heq] at hb
  have hs := coefficient_split328 (Finset.Icc 1 X)
    (fun N => minorError150 ϕ G X N ϑ η) (fun N => minorBare328 ϕ X N ϑ)
  dsimp [minorWeighted328] at hw
  nlinarith only [hs, hb, hw]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minor_budget_identity451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_log9_uniform451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_family_log9_uniform451
