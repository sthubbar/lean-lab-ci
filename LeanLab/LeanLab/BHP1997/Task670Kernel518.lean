/-
P0069 Baker Harman Pintz 1997, pages 3, 43 and 44.
The existing kernel inequality extends to the full factor six window range.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Lemma29
namespace LeanLab.BHP1997.Task670Kernel518
open Complex
/-- P0069 page 44 kernel inequality with the factor six in the page 3 window range.
The constant 324 absorbs the replacement of T by T divided by six. -/
theorem lemma29_six_kernel {t z T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hT : 0 < T) (hzT : z ≤ 6 / T) :
    ‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
        ‖(1 / 2 + t * I : ℂ)‖ ^ 2 ≤ 324 / (T ^ 2 + t ^ 2) := by
  have hT6 : 0 < T / 6 := by positivity
  have hz6 : z ≤ 1 / (T / 6) := by
    have he : (1 : ℝ) / (T / 6) = 6 / T := by field_simp
    rw [he]; exact hzT
  refine (LeanLab.BHP1997.Lemma29.lemma29_ineq hz hz1 hT6 hz6).trans ?_
  have hd : 0 < T ^ 2 + t ^ 2 := by positivity
  have hd6 : 0 < (T / 6) ^ 2 + t ^ 2 := by positivity
  apply (div_le_div_iff₀ hd6 hd).mpr
  nlinarith [sq_nonneg t]

end LeanLab.BHP1997.Task670Kernel518
