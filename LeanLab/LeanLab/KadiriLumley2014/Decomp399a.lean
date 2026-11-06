/-
P0059 arXiv 1407.7902v1 page 7 Lemma 2.5.
Written derivation: arXiv 1310.6374 pages 8 to 10, Section 2.3.
Five independent weighted zero estimates replace the combined proof task.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259
import LeanLab.KadiriLumley2014.DensityBound399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set
open Task259

/-- LEAF. Page 7 display 2.45. Source 4, arXiv 1310.6374 pages 8 and 9,
Corollary 2.6 and display 2.22, applies the Rosser count bound to the reciprocal
ordinate on the finite interval. Only the Rosser input is needed. -/
theorem reciprocal_interval {T1 : ℝ}
    (hT0 : 1132491 ≤ T1) (hCount : RosserCountBound) :
    positiveZeroSum (fun ρ => if 1132491 < ρ.im ∧ ρ.im ≤ T1 then 1 / ρ.im else 0) ≤
      zeroS1 T1 := by
  sorry

/-- LEAF. Page 7 display 2.46. Source 4, arXiv 1310.6374 pages 8 and 9,
Corollary 2.6 and display 2.23, applies the Rosser count bound to the reciprocal
power on the finite interval. No verified RH height or density input is needed. -/
theorem power_interval {m : ℕ} {T1 : ℝ}
    (hm : 2 ≤ m) (hT0 : 1132491 ≤ T1) (hTH : T1 ≤ 30610000000)
    (hCount : RosserCountBound) :
    positiveZeroSum (fun ρ => if T1 < ρ.im ∧ ρ.im ≤ 30610000000 then
      1 / ρ.im ^ (m + 1) else 0) ≤ zeroS2 m T1 := by
  sorry

/-- LEAF. Page 7 display 2.47. Source 4, arXiv 1310.6374 pages 8 and 9,
Corollary 2.6 and display 2.24, sends the upper endpoint of the reciprocal power
estimate to infinity. Only the Rosser count input is needed. -/
theorem power_tail {m : ℕ} (hm : 2 ≤ m) (hCount : RosserCountBound) :
    positiveZeroSum (fun ρ => if 30610000000 < ρ.im then
      1 / ρ.im ^ (m + 1) else 0) ≤ zeroS3 m := by
  sorry

/-- LEAF. Page 7 display 2.48. Source 4, arXiv 1310.6374 page 9,
Lemma 2.7 and display 2.25. Integrate the density count against the derivative
of the reciprocal power. Verified RH height removes the lower boundary count. -/
theorem density_power_tail {m : ℕ} {σ c1 c2 c3 : ℝ}
    (hm : 2 ≤ m) (hσ : 3 / 5 < σ) (hσ1 : σ < 1)
    (hRH : VerifiedHeight 30610000000)
    (hDensity : DensityBound σ c1 c2 c3) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    positiveZeroSum (fun ρ => if 30610000000 < ρ.im ∧ σ < ρ.re then
      1 / ρ.im ^ (m + 1) else 0) ≤ zeroS4 m c1 c2 c3 := by
  have h := density_power_tail_bound (m := m) (by omega)
    (by norm_num : (0 : ℝ) < 30610000000) (by linarith : (1 / 2 : ℝ) < σ)
    hRH hDensity hc1 hc2
  apply h.trans_eq
  unfold densityPrimitive zeroS4
  rw [pow_succ]
  field_simp
  <;> ring

/-- LEAF. Page 7 display 2.49. Source 4, arXiv 1310.6374 pages 9 and 10,
Lemma 2.7 and displays 2.26 to 2.30. Integrate the density count against the
weighted reciprocal power, then bound its remaining integral as in display 2.29.
The zero-free region motivates the weight but is not needed to estimate this sum. -/
theorem density_weighted_tail {m : ℕ} {X σ c1 c2 c3 : ℝ}
    (hm : 2 ≤ m) (hX : 10 < X) (hσ : 3 / 5 < σ) (hσ1 : σ < 1)
    (hRH : VerifiedHeight 30610000000)
    (hDensity : DensityBound σ c1 c2 c3) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hlog : Real.log X < 5.69693 * m * (Real.log 30610000000) ^ 2) :
    positiveZeroSum (fun ρ => if 30610000000 < ρ.im ∧ σ < ρ.re then
      X ^ (-1 / (5.69693 * Real.log ρ.im)) / ρ.im ^ (m + 1) else 0) ≤
      zeroS5 X m c1 c2 c3 * X ^ (-1 / (5.69693 * Real.log 30610000000)) := by
  sorry

/-- Page 7 Lemma 2.5. Exact statement of Task259.lemma2_5_positive assembled
from its five strictly smaller estimates. CONDITIONAL ON the five OPEN leaves. -/
theorem lemma2_5_positive (m : ℕ) {T1 X σ c1 c2 c3 : ℝ}
    (hm : 2 ≤ m) (hX : 10 < X) (hT0 : 1132491 ≤ T1) (hTH : T1 ≤ 30610000000)
    (hσ : 3 / 5 < σ) (hσ1 : σ < 1)
    (hRH : VerifiedHeight 30610000000) (hLow : LowZeroData 1132491 2001052 11.637732363)
    (hZF : ZeroFreeRegion 5.69693) (hCount : RosserCountBound)
    (hDensity : DensityBound σ c1 c2 c3) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hlog : Real.log X < 5.69693 * m * (Real.log 30610000000) ^ 2) :
    Lemma25Bounds m T1 X σ c1 c2 c3 := by
  exact ⟨reciprocal_interval hT0 hCount,
    power_interval hm hT0 hTH hCount,
    power_tail hm hCount,
    density_power_tail hm hσ hσ1 hRH hDensity hc1 hc2,
    density_weighted_tail hm hX hσ hσ1 hRH hDensity hc1 hc2 hlog⟩

end LeanLab.KadiriLumley2014.Task399
