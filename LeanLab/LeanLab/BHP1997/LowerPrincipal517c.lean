/-
P0069 Baker, Harman and Pintz 1997, Section 5, pages 51 and 52, the U-1624 normalization:
the clipping of the lab factor is inactive on J for large x, from the slope leaf.
No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LowerPrincipal517a

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 pages 51 and 52 with the U-1624 normalization: for large `x` and every `m` in J the
factor times the local density of the raw coefficient is exactly the constant center
`v0 / log Y` of display 1.8. CONDITIONAL on the open leaf `leaf_density_slope`. -/
theorem factor_density_center (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m ∈ rightInterval ε x,
      lowerFactor ω ε x m *
        (lowerDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x)) =
          lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) := by
  obtain ⟨hv0, s0, hs0, hV⟩ := leaf_density_slope ω hω hz hε hε8
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine ⟨Real.exp (2 * max (2 * Real.log 4) (Real.log 4 / (1 - s0))), fun x hx m hm => ?_⟩
  have hK1 : 2 * Real.log 4 ≤ max (2 * Real.log 4) (Real.log 4 / (1 - s0)) := le_max_left _ _
  have hK2 : Real.log 4 / (1 - s0) ≤ max (2 * Real.log 4) (Real.log 4 / (1 - s0)) :=
    le_max_right _ _
  generalize max (2 * Real.log 4) (Real.log 4 / (1 - s0)) = K at hx hK1 hK2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 2 * K ≤ Real.log x := by
    rw [← Real.log_exp (2 * K)]; exact Real.log_le_log (Real.exp_pos _) hx
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hLY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x := Real.log_rpow hx0 _
  have hLYK : K ≤ Real.log (x ^ (11 / 20 + ε)) := by rw [hLY]; nlinarith
  have hLZ : Real.log (scaleZ ε x) = 2 * Real.log 2 + Real.log (x ^ (11 / 20 + ε)) := by
    unfold scaleZ shortY; rw [Real.log_mul (by norm_num) hY0.ne', h4]
  rw [rightInterval, Finset.mem_Ioc] at hm
  have hmY : x ^ (11 / 20 + ε) < (m : ℝ) := Nat.lt_of_floor_lt hm.1
  have hm2 : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    (Nat.cast_le.mpr hm.2).trans (Nat.floor_le (by positivity))
  have hm0 : 0 < (m : ℝ) := hY0.trans hmY
  have hLm1 : Real.log (x ^ (11 / 20 + ε)) < Real.log m := Real.log_lt_log hY0 hmY
  have hLm2 : Real.log m ≤ Real.log 2 + Real.log (x ^ (11 / 20 + ε)) := by
    rw [← Real.log_mul (by norm_num) hY0.ne']; exact Real.log_le_log hm0 hm2
  unfold lowerFactor
  rw [hLZ]
  rw [h4] at hK1 hK2
  generalize Real.log (x ^ (11 / 20 + ε)) = LY at *
  generalize Real.log (m : ℝ) = Lm at *
  generalize Real.log 2 = l at *
  have hLYpos : 0 < LY := by nlinarith
  have hLZpos : 0 < 2 * l + LY := by positivity
  have hs0' : 0 < 1 - s0 := by linarith
  have hK2' : 2 * l ≤ LY * (1 - s0) := by
    have := hK2.trans hLYK
    rwa [div_le_iff₀ hs0'] at this
  have hs1 : s0 ≤ Lm / (2 * l + LY) := by
    rw [le_div_iff₀ hLZpos]; nlinarith
  have hs2 : Lm / (2 * l + LY) ≤ 1 := by
    rw [div_le_one hLZpos]; linarith
  have hs := hV _ hs1 hs2
  have he : l / (2 * l + LY) ≤ 1 - Lm / (2 * l + LY) := by
    rw [show 1 - Lm / (2 * l + LY) = (2 * l + LY - Lm) / (2 * l + LY) by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hLZpos.le
  generalize lowerDensityAt ω ε (Lm / (2 * l + LY)) = V at *
  have hV' : lowerV0 ω ε * (1 + 3 * (l / (2 * l + LY))) ≤ V := by nlinarith
  rcases hv0.eq_or_lt with h0 | hpos
  · simp [← h0]
  · have hpos1 : 0 < 1 + 3 * (l / (2 * l + LY)) := by positivity
    have hVpos : 0 < V := lt_of_lt_of_le (mul_pos hpos hpos1) hV'
    have hq : 2 * l + LY ≤ LY * (1 + 3 * (l / (2 * l + LY))) := by
      rw [show LY * (1 + 3 * (l / (2 * l + LY))) = LY * (2 * l + LY + 3 * l) / (2 * l + LY) by
        field_simp]
      rw [le_div_iff₀ hLZpos]; nlinarith
    have hnum : lowerV0 ω ε * (2 * l + LY) ≤ LY * V := by
      calc lowerV0 ω ε * (2 * l + LY) ≤ lowerV0 ω ε * (LY * (1 + 3 * (l / (2 * l + LY)))) :=
            mul_le_mul_of_nonneg_left hq hpos.le
        _ = LY * (lowerV0 ω ε * (1 + 3 * (l / (2 * l + LY)))) := by ring
        _ ≤ LY * V := mul_le_mul_of_nonneg_left hV' hLYpos.le
    have hR1 : lowerV0 ω ε * (2 * l + LY) / (LY * V) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hnum
    have hR0 : 0 ≤ lowerV0 ω ε * (2 * l + LY) / (LY * V) := by positivity
    rw [min_eq_right hR1, max_eq_right hR0]
    field_simp

end LeanLab.BHP1997.LowerShortC165
