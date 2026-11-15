/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 46, 47, 51 and 52.
The discrete radial bound with an explicit terminal mass.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Helfgott2013.Decomp1538a
import LeanLab.Helfgott2013.SectionSeven

namespace LeanLab.Ternary.Task580
open Finset

/-- The terminal mass stays separate from the cumulative interior budget.
Helfgott page 46 equation 6.2 and page 47 Abel summation, applied to the
terminal shell in the Theorem 6.3 proof on pages 51 and 52 before equation 6.19.
This finite form permits a jump at the terminal radius.
CONDITIONAL ON the explicit prefix mass bounds. -/
theorem radial_sum_with_terminal_mass (f g F : ℕ → ℝ) {a b : ℕ}
    (hab : a ≤ b) (hprefix : ∀ n ∈ Icc a b, ∑ m ∈ Icc a n, f m ≤ F n)
    (hg : AntitoneOn g (Set.Icc a (b + 1))) (tail W : ℝ)
    (hW : (∑ n ∈ Icc a b, f n) + tail = W) :
    (∑ n ∈ Icc a b, f n * g n) + tail * g (b + 1) ≤
      g a * F a + (∑ n ∈ Ico a b, g (n + 1) * (F (n + 1) - F n)) +
        g (b + 1) * (W - F b) := by
  have hstep :
      (∑ n ∈ Icc a b, f n) * (g b - g (b + 1)) +
        (∑ n ∈ Ico a b, (∑ m ∈ Icc a n, f m) * (g n - g (n + 1))) ≤
      F b * (g b - g (b + 1)) +
        (∑ n ∈ Ico a b, F n * (g n - g (n + 1))) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (hprefix b (mem_Icc.mpr ⟨hab, le_rfl⟩))
        (sub_nonneg.mpr (hg ⟨hab, Nat.le_succ b⟩ ⟨by omega, le_rfl⟩ (Nat.le_succ b)))
    · apply sum_le_sum
      intro n hn
      have hn' := mem_Ico.mp hn
      apply mul_le_mul_of_nonneg_right (hprefix n (Ico_subset_Icc_self hn))
      apply sub_nonneg.mpr
      exact hg ⟨hn'.1, by omega⟩ ⟨by omega, by omega⟩ (Nat.le_succ n)
  have hid := LeanLab.Helfgott2013.U1538.sum_by_parts f g hab
  have hrewrite := LeanLab.Helfgott2013.U1538.by_parts_rearrange F g hab
  have htotal := congrArg (fun z : ℝ => z * g (b + 1)) hW
  nlinarith only [hstep, hid, hrewrite, htotal]

/-- The v2 page 62 rounding does not follow from its page 49 coefficient.
Helfgott page 49 equation 6.11 and page 62 last display.
This diagnostic concerns the printed scalar substitution alone. -/
theorem v2_remainder_rounding_exceeds_printed :
    (0.60579 : ℝ) < 0.51942 * 1.079955 ^ 2 := by norm_num

/-- The book rounding covers the same scalar substitution.
Helfgott book 1501.05438 page 268 display before equation 14.28. -/
theorem book_remainder_rounding_covers :
    (0.51942 : ℝ) * 1.079955 ^ 2 ≤ 0.60581 := by norm_num

/-- Directly scaling the lab Corollary 1.3 error budget gives a ceiling
larger than the desired star first moment allowance at the threshold.
Helfgott page 59 equation 7.16 and Hela Corollary 1.3 as encoded in the lab.
This compares upper bound functions, not the actual arithmetic error. -/
theorem scaled_cor13_budget_exceeds_star_allowance :
    (1.9075e-8 : ℝ) < 4.269e-14 +
      (380600 + 76) / Real.sqrt (4.9e26 / 49) := by
  have hs : Real.sqrt (4.9e26 / 49 : ℝ) < 3.2e12 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hp : 0 < Real.sqrt (4.9e26 / 49 : ℝ) := by positivity
  have he : (1e-7 : ℝ) < (380600 + 76) / Real.sqrt (4.9e26 / 49) :=
    (lt_div_iff₀ hp).mpr (by nlinarith)
  linarith

/-- The corrected book coefficient envelope has the stated uniform E budget.
Helfgott book 1501.05438 page 268 equation 14.28.
The existing logarithmic comparison controls every x above the threshold. -/
theorem book_E_bound {x : ℝ} (hx : 4.9e26 ≤ x) :
    (2.94325 * Real.log x + 5.12426) * Real.sqrt x ≤ 8.4029e-12 * x := by
  have hx0 : 0 ≤ x := by linarith
  have hl := LeanLab.Helfgott2013.log_x_le hx
  have hu0 : (2.2135943e13 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0]
    linarith
  set u := Real.sqrt x with hu
  have hux : u * u = x := Real.mul_self_sqrt hx0
  have huPos : 0 < u := by linarith
  have key : 2.94325 * Real.log x + 5.12426 ≤ 8.4029e-12 * u := by
    have hdiv : u / 2.2135943e13 = u * (1 / 2.2135943e13) := by ring
    rw [hdiv] at hl
    have hc : (0 : ℝ) ≤ 8.4029e-12 - 2.94325 * 2 * (1 / 2.2135943e13) := by norm_num
    have hstep := mul_le_mul_of_nonneg_left hu0 hc
    have hbase : 2.94325 * (2 * (30.7282275 - 1)) + 5.12426 ≤
        (8.4029e-12 - 2.94325 * 2 * (1 / (2.2135943e13 : ℝ))) * 2.2135943e13 := by
      norm_num
    nlinarith
  calc
    (2.94325 * Real.log x + 5.12426) * u ≤ 8.4029e-12 * u * u :=
      mul_le_mul_of_nonneg_right key huPos.le
    _ = 8.4029e-12 * x := by rw [← hux]; ring

end LeanLab.Ternary.Task580
