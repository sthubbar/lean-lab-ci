/-
P0022, page 362. The tapered von Mangoldt weight as a positive part difference
and a logarithmic box average. This isolates an elementary kernel in display 2.
It does not prove the cited Selberg contour identity.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.Statements

namespace LeanLab.KanieckiGap.Taper127

open LeanLab.Kaniecki1995 Real MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt

/-- Page 362. On the paper support, the logarithmic taper is a difference of positive parts. -/
theorem weight_positive_part {x a : ℝ} (hx : 1 < x) (ha : 1 < a) (n : ℕ)
    (hn : 0 < n) (hns : (n : ℝ) ≤ x ^ a) :
    LamXA x a n = Λ n *
      (max (a * Real.log x - Real.log n) 0 - max (Real.log x - Real.log n) 0) /
        ((a - 1) * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log x := Real.log_pos hx
  have hLA : Real.log x < a * Real.log x := by nlinarith
  have hD : (a - 1) * Real.log x ≠ 0 := by positivity
  have hnu : Real.log n ≤ a * Real.log x := by
    have h := Real.log_le_log hn0 hns
    rwa [Real.log_rpow hx0] at h
  unfold LamXA
  by_cases hnx : (n : ℝ) ≤ x
  · rw [if_pos hnx]
    have hnl := Real.log_le_log hn0 hnx
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    apply (eq_div_iff hD).mpr
    ring
  · rw [if_neg hnx]
    have hln := Real.log_le_log hx0 (le_of_lt (lt_of_not_ge hnx))
    rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    rw [Real.log_div (Real.rpow_pos_of_pos hx0 a).ne' hn0.ne', Real.log_rpow hx0]
    ring

/-- Page 362. The step function average equals the positive part difference.
This is the elementary logarithmic kernel underlying the taper. -/
theorem step_integral {L A u : ℝ} (hLA : L ≤ A) (huA : u ≤ A) :
    (∫ t in L..A, if u ≤ t then (1 : ℝ) else 0) =
      max (A - u) 0 - max (L - u) 0 := by
  by_cases huL : u ≤ L
  · calc
      (∫ t in L..A, if u ≤ t then (1 : ℝ) else 0) = ∫ _ in L..A, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hLA
        intro t ht
        simp only [ite_eq_left (huL.trans ht.1.le)]
      _ = A - L := by simp
      _ = max (A - u) 0 - max (L - u) 0 := by
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        ring
  · have hLu : L ≤ u := by linarith
    have hint (b c : ℝ) :
        IntervalIntegrable (fun t => if u ≤ t then (1 : ℝ) else 0) volume b c := by
      have h := intervalIntegrable_const (μ := volume) (a := b) (b := c) (c := (1 : ℝ))
      exact ⟨h.1.indicator measurableSet_Ici, h.2.indicator measurableSet_Ici⟩
    have hleft : (∫ t in L..u, if u ≤ t then (1 : ℝ) else 0) = 0 := by
      calc
        _ = ∫ _ in L..u, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hLu
          intro t ht
          simp only [ite_eq_right (not_le.mpr ht.2)]
        _ = 0 := by simp
    have hright : (∫ t in u..A, if u ≤ t then (1 : ℝ) else 0) = A - u := by
      calc
        _ = ∫ _ in u..A, (1 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le huA
          intro t ht
          simp only [ite_eq_left ht.1.le]
        _ = A - u := by simp
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint L u) (hint u A), hleft,
      hright, max_eq_left (by linarith), max_eq_right (by linarith)]
    ring

/-- Page 362, display 2. The taper is a logarithmic box average of a cutoff.
Only the kernel identity is proved here, not the explicit formula over zeros. -/
theorem weight_integral {x a : ℝ} (hx : 1 < x) (ha : 1 < a) (n : ℕ)
    (hn : 0 < n) (hns : (n : ℝ) ≤ x ^ a) :
    LamXA x a n = Λ n *
      (∫ t in Real.log x..a * Real.log x, if Real.log n ≤ t then (1 : ℝ) else 0) /
        ((a - 1) * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnu : Real.log n ≤ a * Real.log x := by
    have h := Real.log_le_log hn0 hns
    rwa [Real.log_rpow hx0] at h
  rw [step_integral (by nlinarith) hnu]
  exact weight_positive_part hx ha n hn hns

/-- Page 362. The nonconstant taper branch has a concrete positive support instance. -/
theorem taper_instance :
    LamXA 2 2 3 = Λ 3 *
      (∫ t in Real.log 2..2 * Real.log 2, if Real.log 3 ≤ t then (1 : ℝ) else 0) /
        Real.log 2 := by
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using weight_integral (x := 2) (a := 2) (by norm_num) (by norm_num) 3
    (by norm_num) (by norm_num)

end LeanLab.KanieckiGap.Taper127

#print axioms LeanLab.KanieckiGap.Taper127.weight_positive_part
#print axioms LeanLab.KanieckiGap.Taper127.step_integral
#print axioms LeanLab.KanieckiGap.Taper127.weight_integral
#print axioms LeanLab.KanieckiGap.Taper127.taper_instance
