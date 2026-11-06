/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 175 to 177, even Taylor truncation in Lemma 4.
-/
import Mathlib

namespace LeanLab.PlattTrudgian2014

open Finset

/-- P0026 page 175, cancellation of the odd Taylor terms before display 4.15. -/
theorem even_taylor_pair380 (y : ℝ) (K : ℕ) :
    (∑ j ∈ range (2 * K), y ^ j / j.factorial) +
      (∑ j ∈ range (2 * K), (-y) ^ j / j.factorial) =
        2 * ∑ j ∈ range K, y ^ (2 * j) / (2 * j).factorial := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by omega]
    simp only [sum_range_succ]
    have he : (-y) ^ (2 * K) = y ^ (2 * K) := by simp [pow_mul]
    have ho : (-y) ^ (2 * K + 1) = -(y ^ (2 * K + 1)) := by simp [pow_succ, he]
    rw [he, ho]
    simp only [neg_div]
    linarith

/-- P0026 page 177, a Taylor remainder with cutoff at least the argument bound. -/
theorem exp_taylor_cutoff380 (y A : ℝ) (hA : 0 ≤ A) (hy : |y| ≤ A)
    (K : ℕ) (hK : A ≤ K) :
    Real.exp y ≤ (∑ j ∈ range (2 * K), y ^ j / j.factorial) +
      2 * A ^ (2 * K) / (2 * K).factorial := by
  have hratio : ‖(y : ℂ)‖ / (2 * K + 1 : ℕ) ≤ (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 * K + 1 : ℕ))]
    push_cast
    linarith
  have hz := Complex.exp_bound' (x := (y : ℂ)) (n := 2 * K) hratio
  have he : ((Real.exp y - ∑ j ∈ range (2 * K), y ^ j / j.factorial : ℝ) : ℂ) =
      Complex.exp (y : ℂ) - ∑ j ∈ range (2 * K), (y : ℂ) ^ j / j.factorial := by
    push_cast
    rfl
  rw [← he, Complex.norm_real, Real.norm_eq_abs] at hz
  have hu := (abs_le.mp hz).2
  have hp := pow_le_pow_left₀ (abs_nonneg y) hy (2 * K)
  have hd : (0 : ℝ) < (2 * K).factorial := by positivity
  have hm := div_le_div_of_nonneg_right hp hd.le
  simp only [Complex.norm_real, Real.norm_eq_abs] at hu
  simp only [mul_div_assoc] at *
  linarith

/-- P0026 pages 176 to 177, the pointwise even Taylor cutoff behind display 4.17. -/
theorem norm_even_taylor_cutoff380 (y A : ℝ) (hy : 0 ≤ y) (hyA : y ≤ A)
    (K : ℕ) (hK : A ≤ K) :
    Real.exp y ≤ 2 * (∑ j ∈ range K, y ^ (2 * j) / (2 * j).factorial) +
      4 * A ^ (2 * K) / (2 * K).factorial := by
  have hA := hy.trans hyA
  have hp := exp_taylor_cutoff380 y A hA (by rwa [abs_of_nonneg hy]) K hK
  have hn := exp_taylor_cutoff380 (-y) A hA (by simpa [abs_of_nonneg hy] using hyA) K hK
  have he := even_taylor_pair380 y K
  simp only [mul_div_assoc] at *
  linarith [Real.exp_pos (-y)]

/-- P0026 page 176, the real even Taylor comparison needs integration.
The corresponding pointwise bound already fails at argument minus one. -/
theorem even_taylor_pointwise_failure380 :
    ¬ (∑ j ∈ range 1, (-1 : ℝ) ^ (2 * j) / (2 * j).factorial) ≤ Real.exp (-1) := by
  simp only [sum_range_one, mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  exact not_le_of_gt (Real.exp_lt_one_iff.mpr (by norm_num))

#print axioms even_taylor_pointwise_failure380
#print axioms even_taylor_pair380
#print axioms exp_taylor_cutoff380
#print axioms norm_even_taylor_cutoff380

end LeanLab.PlattTrudgian2014
