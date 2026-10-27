/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Elementary consequences of the c_r recursion.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveFns

namespace LeanLab.Akeno2026.SieveFns
open Real Set MeasureTheory intervalIntegral

/-- The nonnegative c_r recursion vanishes at every argument at most its starting point. -/
theorem cR_eq_zero_of_le (r : ℕ) {x : ℝ} (hx : x ≤ (r : ℝ) + 2) :
    cR (r + 2) x = 0 := by
  apply le_antisymm
  · have h := (cR_mono_nonneg (r + 2)).1 hx
    simpa only [cR_base] using h
  · exact (cR_mono_nonneg (r + 2)).2 x

/-- The r = 2 direct calculation on page 36 gives c2(s) = log(s - 1). -/
theorem cR_two_eq_log {s : ℝ} (hs : 2 ≤ s) : cR 2 s = log (s - 1) := by
  have h := cR_delay 0 (a := 2) (b := s) (by norm_num) hs
  have hz : cR 2 2 = 0 := by simpa using cR_base 0
  rw [hz, sub_zero] at h
  calc
    cR 2 s = ∫ u in (2 : ℝ)..s, cR 1 (u - 1) / (u - 1) := h
    _ = ∫ u in (2 : ℝ)..s, (u - 1)⁻¹ := by
      apply integral_congr
      intro u hu
      rw [uIcc_of_le hs] at hu
      dsimp only
      rw [cR_one (by linarith [hu.1])]
      simp
    _ = log (s - 1) := by
      convert (weight_shift (by norm_num : (1 : ℝ) < 2) hs).1 using 1; norm_num

theorem cR_two_pos {s : ℝ} (hs : 2 < s) : 0 < cR 2 s := by
  rw [cR_two_eq_log hs.le]
  exact log_pos (by linarith)

/-- The c1 cutoff is zero strictly below 1. -/
theorem cR_one_eq_zero {x : ℝ} (hx : x < 1) : cR 1 x = 0 := by
  simp only [cR, ite_eq_right (not_le.mpr hx)]

end LeanLab.Akeno2026.SieveFns
