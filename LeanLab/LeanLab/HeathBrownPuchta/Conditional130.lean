import LeanLab.HeathBrownPuchta.SReduction
import LeanLab.HeathBrownPuchta.Decomp1530b

/-!
P0012 page 21, the C2 series convergence input of Lemma 8.
Page 26 gives the logarithmic partial sum bound via Liu Liu Wang display 3.9.
The generic summability implication is elementary.
The specialization to LLW remains CONDITIONAL ON that cited input.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.HeathBrownPuchta.Conditional130

open Finset Real
open LeanLab.HeathBrownPuchta.Lemma8Const
open LeanLab.HeathBrownPuchta.SReduction

/-- Logarithmic partial sums imply convergence of the reciprocal weighted series.
Paper page 26, the tail estimate before display 41. -/
theorem summable_of_log_bound (κ : ℕ → ℝ) (hκ : ∀ e, 0 ≤ κ e)
    (hS : ∀ n, 24 ≤ n → ∑ e ∈ range n, κ (e + 1) ≤ 2744 / 1000 * Real.log n) :
    Summable fun e : ℕ => κ (e + 1) / ((e : ℝ) + 1) := by
  apply summable_of_sum_range_le (c := LeanLab.HeathBrownPuchta.Lemma8Const.P κ (2744 / 1000) 24)
    (fun e => div_nonneg (hκ _) (by positivity))
  intro n
  rcases le_total 24 n with hn | hn
  · exact tail_partial κ (by norm_num) (by norm_num) hS n hn
  · calc
      ∑ e ∈ range n, κ (e + 1) / ((e : ℝ) + 1) ≤
          ∑ e ∈ range 24, κ (e + 1) / ((e : ℝ) + 1) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hn)
          (fun e _ _ => div_nonneg (hκ _) (by positivity))
      _ ≤ _ := tail_partial κ (by norm_num) (by norm_num) hS 24 le_rfl

/-- The open convergence input of Lemma 8, CONDITIONAL ON LLW display 3.9,
as used on paper page 26. -/
theorem C2_summable_of_LLW (hL : LLW) :
    Summable fun e : ℕ => kappaTrue (e + 1) / ((e : ℝ) + 1) :=
  summable_of_log_bound kappaTrue kappaTrue_nonneg (llw_input hL)

end LeanLab.HeathBrownPuchta.Conditional130
