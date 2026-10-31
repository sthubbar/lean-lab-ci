/-
P0087 Akeno 2026 page 6, the Type II phase correlation.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026.Phase86
open LeanLab.Akeno2026
/-- LEAF. Page 6, multiplying a phase by a conjugate subtracts its argument. -/
theorem phase_correlation (x y : ℝ) : e x * star (e y) = e (x - y) := by
  change e x * (starRingEnd ℂ) (e y) = e (x - y)
  unfold e
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- LEAF. Page 6, correlation of phases and real weights gives the displayed difference phase. -/
theorem kernel_correlation (β m n₁ n₂ u v : ℝ) :
    (e (β * m * n₁) * (u : ℂ)) * star (e (β * m * n₂) * (v : ℂ)) =
      e (β * (n₁ - n₂) * m) * (u : ℂ) * (v : ℂ) := by
  calc
    _ = (e (β * m * n₁) * star (e (β * m * n₂))) * (u : ℂ) * (v : ℂ) := by
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    _ = _ := by
      rw [phase_correlation]
      have hid : β * m * n₁ - β * m * n₂ = β * (n₁ - n₂) * m := by ring
      rw [hid]

end LeanLab.Akeno2026.Phase86
