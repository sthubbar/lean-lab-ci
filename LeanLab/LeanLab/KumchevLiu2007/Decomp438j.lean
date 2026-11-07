/-
Numerical smooth tail supply for three-square truncation.
Source page 14 below display 50. The numerical leaf remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438i
import LeanLab.KumchevLiu2007.Decomp447b

namespace LeanLab.KumchevLiu2007.Task438j

open Real Complex Task129b Task129c Task292c Task438d
open scoped BigOperators

/-- LEAF. Page 14 below display 50, using Lemma 3.5 on page 12.
This is only a numerical weighted smooth reciprocal tail. There is no A3,
n, Euler product, series error or interval average. The proved conservative
majorant has one factor 64 per distinct prime divisor. -/
theorem smooth_reciprocal_tail (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        smoothWeight q Q * (coefficientMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  exact Task447b.smooth_reciprocal_tail A ε hA hε

/-- Page 14 below display 50. The proved composite estimate bounds the
norm of the smooth coefficient tail by its numerical majorant. -/
theorem smooth_tail_norm (n : ℕ) (T Q : ℝ) :
    ‖∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
      (smoothWeight q Q : ℂ) * A3 n q‖ ≤
    ∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
      smoothWeight q Q * (coefficientMajorant q / (q : ℝ)) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
        ‖(smoothWeight q Q : ℂ) * A3 n q‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hw : 0 ≤ smoothWeight q Q := by unfold smoothWeight; split <;> norm_num
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (coefficient_product_bound n q hqn) hw

/-- Page 14 below display 50. Exact Task438a pointwise tail statement.
CONDITIONAL only on the numerical smooth_reciprocal_tail leaf. -/
theorem smooth_tail_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q‖ ^ 2 ≤
          C / Real.log x ^ A := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := smooth_reciprocal_tail A ε hA hε
  refine ⟨C ^ 2, x0, by positivity, hx0, ?_⟩
  intro x y Q hx hy hyx hQpos hQ n
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ ≤ (C / Real.log x ^ (A / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        ((smooth_tail_norm n _ Q).trans (hb x y Q hx hy hyx hQpos hQ)) 2
    _ = C ^ 2 / Real.log x ^ A := by
      have hp : (Real.log x ^ (A / 2)) ^ (2 : ℕ) = Real.log x ^ A := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
        congr 1
        push_cast
        ring
      rw [div_pow, hp]

#print axioms smooth_reciprocal_tail
#print axioms smooth_tail_norm
#print axioms smooth_tail_pointwise

end LeanLab.KumchevLiu2007.Task438j
