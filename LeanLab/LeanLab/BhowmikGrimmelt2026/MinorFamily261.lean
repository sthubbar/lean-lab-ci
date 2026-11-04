/-
A weaker true logarithm power for the actual minor family.
Source: P0029 pages 26 and 27, displays 7.5 and 7.8.
The bound retains the Poisson remainder and uses logarithm power ten.
It does not discharge the sealed printed logarithm power five leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ArcFamily261
import LeanLab.BhowmikGrimmelt2026.PartialSums261
import LeanLab.BhowmikGrimmelt2026.SupportedFamily261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped NNReal

attribute [local instance] Classical.propDecidable

/-- The actual minor family satisfies a power ten logarithm bound with the Poisson remainder. -/
theorem minor_family_log10_remainder261 {ϕ G : ℝ → ℝ}
    (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ R η : ℝ,
      1 ≤ R → R ≤ X → 0 < η → η ≤ 1 → 10 * R ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, if MajorArc X R α then 0 else
          Sphi ϕ N α ^ 2 * (1 - bRhat G R (fun q => η * X * q / R) α) *
            ee (-(N * α))‖ ^ 2 ≤
          C * (1 + R ^ 2 * (η * X / R ^ 2) ^ (-A)) ^ 2 *
            ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) * X * Real.log X ^ 10 := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  obtain ⟨D, hD⟩ := lemma72 G hG A hA
  let D' : ℝ := 1 + max D 1
  have hD' : 0 ≤ D' := by dsimp [D']; linarith [le_max_right D 1]
  refine ⟨144 * (48600 : ℝ) ^ 2 * D' ^ 2 * (L : ℝ) ^ 4, by positivity, ?_⟩
  intro X hX R η hR hRX hη hη1 hscale
  have hRpos : 0 < R := by linarith
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ X by exact_mod_cast hX)
    linarith [Real.log_two_gt_d9]
  have hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < η * X * q / R := by
    intro q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    positivity
  let E : ℝ := R ^ 2 * (η * X / R ^ 2) ^ (-A)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else
    1 - bRhat G R (fun q => η * X * q / R) α
  let B : ℝ := D' * (1 + E)
  let V : ℝ := 48600 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 4
  let U : ℝ := (L : ℝ) * V
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hU : 0 ≤ U := by dsimp [U, V]; positivity
  have hW : Measurable W :=
    measurable_const.ite (measurableSet_majorArc84 X R)
      ((continuous_const.sub (continuous_bRhat hG.supp hG.even R _ hT)).measurable)
  have hWB (α : ℝ) : ‖W α‖ ≤ B := by
    by_cases hm : MajorArc X R α
    · simp only [W, if_pos hm, norm_zero]
      exact hB
    · dsimp [W]
      rw [if_neg hm]
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖bRhat G R (fun q => η * X * q / R) α‖ := norm_sub_le _ _
        _ ≤ 1 + D * (1 + E) := by
          rw [norm_one]
          have hb := (hD X R η hR hη hη1 hscale α).2 hm
          change ‖bRhat G R (fun q => η * X * q / R) α‖ ≤ D * (1 + E) at hb
          linarith
        _ ≤ 1 + max D 1 * (1 + E) := by
          have hh := mul_le_mul_of_nonneg_right (le_max_left D 1) (by positivity : 0 ≤ 1 + E)
          linarith
        _ ≤ B := by dsimp [B, D']; nlinarith
  have hsup (n : ℕ) (hn : n ≤ X) (α : ℝ) (hne : W α ≠ 0) : ‖Sphi ϕ n α‖ ≤ U := by
    have hm : ¬ MajorArc X R α := by
      intro hh
      exact hne (by simp [W, hh])
    exact Sphi_minor261 hϕ hL hX hR hRX hn hm
  have hfam := supported_family261 hϕ hL hX hW hB hU hWB hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, if MajorArc X R α then 0 else
        Sphi ϕ N α ^ 2 * (1 - bRhat G R (fun q => η * X * q / R) α) *
          ee (-(N * α))) =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  have hA2 : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRpos.le]
  have hD2 : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    norm_num
  have hsq : ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 ≤
      2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA2, ← hD2]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  have hlogs : Real.log (X : ℝ) * (1 + Real.log X) ≤ 3 * Real.log X ^ 2 := by
    nlinarith
  simp_rw [heq]
  calc
    _ ≤ 24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X * (1 + Real.log X) := hfam
    _ ≤ 72 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlogs
        (by positivity : 0 ≤ 24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X)]
    _ = 72 * (48600 : ℝ) ^ 2 * D' ^ 2 * (L : ℝ) ^ 4 * (1 + E) ^ 2 *
        ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 * X * Real.log X ^ 10 := by
      dsimp [B, U, V]
      ring
    _ ≤ 72 * (48600 : ℝ) ^ 2 * D' ^ 2 * (L : ℝ) ^ 4 * (1 + E) ^ 2 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 10 := by
      gcongr
    _ = _ := by dsimp [E]; ring

/-- The optimized minor contribution in display 7.9 with the proved logarithm power ten. -/
theorem minor_family_optimized_log10_261 {ϕ G : ℝ → ℝ}
    (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 4 / 9) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖minorError150 ϕ G X N ϑ (((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ))‖ ^ 2 ≤
          C * ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) *
            X * Real.log X ^ 10 := by
  obtain ⟨A, hA, htail⟩ := optimized_tail261 hϑ hϑ'
  obtain ⟨C, hC, hbound⟩ := minor_family_log10_remainder261 hϕ hG A hA
  refine ⟨4 * C, by positivity, ?_⟩
  intro X hX hscale
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hRX : (X : ℝ) ^ ϑ ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  have hRpos : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXpos ϑ
  have hηpos : 0 < ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hRpos _
  have hη1 : ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR1 (by norm_num)
  let E : ℝ := ((X : ℝ) ^ ϑ) ^ 2 *
    (((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X / ((X : ℝ) ^ ϑ) ^ 2) ^ (-A)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hE1 : E ≤ 1 := by
    dsimp [E]
    rw [htail X hXpos]
    exact pow_le_one₀ hηpos.le hη1
  have hsq : (1 + E) ^ 2 ≤ 4 := by nlinarith
  have hb := hbound X hX ((X : ℝ) ^ ϑ) (((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ))
    hR1 hRX hηpos hη1 hscale
  change (∑ N ∈ Finset.Icc 1 X,
    ‖minorError150 ϕ G X N ϑ (((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ))‖ ^ 2) ≤
      C * (1 + E) ^ 2 *
        ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * X * Real.log X ^ 10 at hb
  apply hb.trans
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity :
    0 ≤ C * ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * X * Real.log X ^ 10)]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minor_family_log10_remainder261

#print axioms LeanLab.BhowmikGrimmelt2026.minor_family_optimized_log10_261
