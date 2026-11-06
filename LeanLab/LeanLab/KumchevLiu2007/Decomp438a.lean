/-
Three-square smooth truncation supplies for page 14 display 50.
The finite identity has a clean supply. The smooth estimate is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp403d
import LeanLab.KumchevLiu2007.Decomp342f
import LeanLab.KumchevLiu2007.Decomp438j

namespace LeanLab.KumchevLiu2007.Task438a

open Real Complex Task129b Task129c Task403c Task292c
open scoped BigOperators

/-- LEAF. Page 14 display 50, from page 13 properties i and ii.
The upper support is four times the product of primes at most Q.
The factor at 2 retains the powers 2, 4 and 8. This is finite algebra only. -/
theorem smooth_remainder_identity (n : ℕ) (P Q T : ℝ)
    (hP : 0 < P) (hPQ : P ≤ Q) (hQT : Q ≤ T) :
    (series3 n P - product3 n Q) - tail3 n P T Q =
      -(∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q) := by
  exact Task438i.smooth_remainder_identity n P Q T hP hPQ hQT

/-- LEAF. Page 14 bound below display 50, using display 47 and Lemma 3.5.
Only the finite smooth coefficient tail remains. There is no P cutoff,
Euler product, subtraction error or average over n in this leaf. -/
theorem smooth_tail_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q‖ ^ 2 ≤
          C / Real.log x ^ A := by
  exact Task438j.smooth_tail_pointwise A ε hA hε

/-- Page 14 display 50. Exact Task403c target from the two smaller leaves.
CONDITIONAL only on Task438j.smooth_reciprocal_tail. -/
theorem truncation_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  obtain ⟨C, xs, hC, hxs, hs⟩ := smooth_tail_pointwise A ε hA hε
  obtain ⟨xt, hxt, ht⟩ := Task342d.cutoff_order ε hε
  refine ⟨2 * C, max xs xt, by positivity, hxs.trans (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxs' : xs ≤ x := (le_max_left _ _).trans hx
  have hxt' : xt ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := hxs.trans hxs'
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  have hQT := ht x y Q hxt' hy hQ
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y, C / Real.log x ^ A := by
      apply Finset.sum_le_sum
      intro n hn
      rw [smooth_remainder_identity n P Q _ hP hPQ hQT, norm_neg]
      exact hs x y Q hxs' hy hyx (hP.trans_le hPQ) hQ n
    _ = ((intervalNumbers x y).card : ℝ) * (C / Real.log x ^ A) := by simp
    _ ≤ (2 * y) * (C / Real.log x ^ A) :=
      mul_le_mul_of_nonneg_right (Task271a.interval_card_le (by linarith) hy1)
        (by positivity)
    _ = (2 * C) * (y / Real.log x ^ A) := by ring

end LeanLab.KumchevLiu2007.Task438a
