/-
P0087 Akeno 2026 pages 31 to 32 and Appendix 5.1 page 36.
The T7 trial improves the conservative total tail without certifying the printed T7 interval.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.T7Trial
import LeanLab.Akeno2026.KuhnTail

namespace LeanLab.Akeno2026.T7Certified
open Set

theorem grid160_enclosure_not_printed :
    ¬ Icc (0.00181842 : ℝ) 0.00181924 ⊆ Icc 0.001818 0.001819 := by
  intro h
  have he := h (show (0.00181924 : ℝ) ∈ Icc 0.00181842 0.00181924 by norm_num)
  norm_num at he

theorem T7_eq_kuhnTr : T7kuhn 33.5 9.5 = KuhnTail.kuhnTr 7 := by
  norm_num [T7kuhn, KuhnTail.kuhnTr]

theorem kuhnTail_bounds_refined :
    (0.00181842 : ℝ) ≤ KuhnTail.kuhnTr 7 + KuhnTail.kuhnTr 8 +
      KuhnTail.kuhnTr 9 + KuhnTail.kuhnTr 10 ∧
    KuhnTail.kuhnTr 7 + KuhnTail.kuhnTr 8 + KuhnTail.kuhnTr 9 +
      KuhnTail.kuhnTr 10 ≤ 0.00208065 := by
  have h7 := T7_bounds_grid160
  rw [T7_eq_kuhnTr] at h7
  obtain ⟨h8l, h8u⟩ := KuhnTail.T8_coarse_bounds
  obtain ⟨h9l, h9u⟩ := KuhnTail.T9_coarse_bounds
  obtain ⟨h10l, h10u⟩ := KuhnTail.T10_coarse_bounds
  constructor <;> linarith [h7.1, h7.2]

theorem m4_refined_tail_margin :
    (0.0327 : ℝ) ≤ 33.5 * 0.56118 - 33.5 * 0.40943 -
      2 / 0.1635 * (0.3689 + 0.04193 + 0.00208065) := by norm_num

end LeanLab.Akeno2026.T7Certified
