/-
Pointwise smooth truncation for Lemma 3.8, page 14 display 50.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp129b

namespace LeanLab.KumchevLiu2007.Task271a

open Real Complex Task129 Task129b
open scoped BigOperators

/-- Page 14 display 49. A real interval of length at least one contains
at most twice its length in natural numbers. -/
theorem interval_card_le {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) :
    ((intervalNumbers x y).card : ℝ) ≤ 2 * y := by
  rw [intervalNumbers, Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : x ≤ x + y))]
  have hu := Nat.floor_le (by linarith : 0 ≤ x + y)
  have hl := Nat.sub_one_lt_floor x
  linarith

/-- LEAF. Page 14 display 50 and the smooth tail estimate below it.
Lemma 3.5 and display 47 give a uniform pointwise remainder with arbitrary
logarithmic decay. This is the square of that remainder bound. The tail
uses minus Psi from direct subtraction, as in the existing definition.
The analytic smooth number estimate remains OPEN. -/
theorem smooth_remainder_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2 ≤
        C / Real.log x ^ A := by
  sorry

/-- Page 14 display 50. The exact truncation_input statement follows
by summing the pointwise remainder. CONDITIONAL on the OPEN leaf. -/
theorem truncation_from_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := smooth_remainder_pointwise A ε hA hε
  refine ⟨2 * C, x0, by positivity, hx0, ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y, C / Real.log x ^ A := by
      apply Finset.sum_le_sum
      intro n hn
      exact hb x y P Q hx hy hyx hP hPQ hQ n
    _ = ((intervalNumbers x y).card : ℝ) * (C / Real.log x ^ A) := by simp
    _ ≤ (2 * y) * (C / Real.log x ^ A) := by
      exact mul_le_mul_of_nonneg_right (interval_card_le (by linarith) hy1)
        (by positivity)
    _ = (2 * C) * (y / Real.log x ^ A) := by ring

/-- Page 4 display 11. The paper's smooth indicator agrees with Mathlib's
smooth numbers at the successor of the natural floor cutoff. -/
theorem smoothWeight_eq_mathlib (q : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) :
    smoothWeight q Q = if q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1) then 1 else 0 := by
  unfold smoothWeight
  congr 1
  rw [Nat.mem_smoothNumbers']
  simp only [Nat.lt_succ_iff, Nat.le_floor_iff hQ]

end LeanLab.KumchevLiu2007.Task271a
