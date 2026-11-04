/-
Smooth remainder in display 50, page 14 of arXiv 0801.0130.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp292b

namespace LeanLab.KumchevLiu2007.Task292c

open Real Complex Task129 Task129b Task292a
open scoped BigOperators

/-- Page 14 before display 50. Q2 is the product of primes at most Q. -/
noncomputable def smoothModulus (Q : ℝ) : ℕ :=
  ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, p

/-- LEAF. Page 14 display 50 and the subtraction immediately below it.
For P at most Q at most T, subtract the finite Euler product expansion
and cancel the coefficients up to P. Only the smooth tail above T
remains. This is an exact finite identity, with no analytic estimate. -/
theorem smooth_remainder_identity (n : ℕ) (P Q T : ℝ)
    (hP : 0 < P) (hPQ : P ≤ Q) (hQT : Q ≤ T) :
    (series2 n P - product2 n Q) - tail2 n P T Q =
      -(∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
        (smoothWeight q Q : ℂ) * U1534.A2 n q) := by
  sorry

/-- LEAF. Page 14 proof of display 50. The allowed Q is eventually
below Q0 equals y to the one third. This is the parameter reduction
needed to cancel the initial segment of the Euler product expansion. -/
theorem cutoff_order (ε : ℝ) (hε : 0 < ε) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      Q ≤ y ^ (1 / 3 : ℝ) := by
  sorry

/-- LEAF. Page 14 smooth tail bound below display 50, from Lemma 3.5
on page 12 and display 47. This numerical weighted smooth reciprocal
tail has no A2 coefficient or singular product. The exponent is A/2
because the target squares the complex norm. -/
theorem smooth_reciprocal_tail (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (smoothModulus Q),
        smoothWeight q Q * (localMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  sorry

/-- Page 14 below display 50. Bound the complex tail by its numerical
majorant. CONDITIONAL on A2_coprime_mul. -/
theorem smooth_tail_norm (n : ℕ) (T Q : ℝ) :
    ‖∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
      (smoothWeight q Q : ℂ) * U1534.A2 n q‖ ≤
    ∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
      smoothWeight q Q * (localMajorant q / (q : ℝ)) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
        ‖(smoothWeight q Q : ℂ) * U1534.A2 n q‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hw : 0 ≤ smoothWeight q Q := by unfold smoothWeight; split <;> norm_num
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (coefficient_product_bound n q hqn) hw

/-- Page 14 display 50. Exact Task271a.smooth_remainder_pointwise
statement. CONDITIONAL on the exact finite identity, cutoff order,
numerical smooth reciprocal tail, and A2_coprime_mul. -/
theorem smooth_remainder_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2 ≤
        C / Real.log x ^ A := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := smooth_reciprocal_tail A ε hA hε
  obtain ⟨x1, hx1, ho⟩ := cutoff_order ε hε
  refine ⟨C ^ 2, max x0 x1, by positivity, hx0.trans (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ n
  have hx0' : x0 ≤ x := (le_max_left _ _).trans hx
  have hx1' : x1 ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := hx0.trans hx0'
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  rw [smooth_remainder_identity n P Q _ hP hPQ (ho x y Q hx1' hy hQ), norm_neg]
  calc
    _ ≤ (C / Real.log x ^ (A / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        ((smooth_tail_norm n _ Q).trans (hb x y Q hx0' hy hyx (hP.trans_le hPQ) hQ)) 2
    _ = C ^ 2 / Real.log x ^ A := by
      have hp : (Real.log x ^ (A / 2)) ^ (2 : ℕ) = Real.log x ^ A := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
        congr 1
        push_cast
        ring
      rw [div_pow, hp]

end LeanLab.KumchevLiu2007.Task292c
