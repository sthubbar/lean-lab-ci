/-
P0093 page 154 equation 2.2 and page 167. Bridge the fresh main coefficient proof.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_count_circle_coefficient357

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 154 equation 2.2. Exact original coefficient type
from the newly proved full tuple identity on main. No new decomposition
of this source blocked target is introduced. -/
theorem count_circle_coefficient_proved435 (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) =
      (Real.exp (-1) : ℂ) * (representationCount111 k N : ℂ) := by
  exact count_circle_coefficient357_split k N hN

/-- P0093 page 167 partition before equation 10.1. Exact
circle_partition280 type through the freshly proved coefficient identity
and the existing measurable partition. Both components are proved. -/
theorem circle_partition_proved435 (k N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    (representationCount111 k N : ℝ) =
      arcContribution280 k N (majorArcs280 N) +
      arcContribution280 k N (exceptionalArcs280 N η) +
      arcContribution280 k N (goodMinorArcs280 N η) := by
  have hS := continuous_prime_fourier111 N hN
  have hT := continuous_power_fourier111 N hN
  have hf : Continuous (fun α : ℝ => primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
      Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by fun_prop
  have hp := integral_circle_partition357 N hN η _ hf
  have hc := congrArg Complex.re (count_circle_coefficient_proved435 k N hN)
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.natCast_re, zero_mul] at hc
  have hid : (representationCount111 k N : ℝ) =
      Real.exp 1 * (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111 N α ^ 2 *
        powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)).re := by
    rw [hc, ← mul_assoc, he, one_mul]
  rw [hid, hp]
  simp only [arcContribution280, Complex.add_re]
  ring


end LeanLab.Linnik1951
