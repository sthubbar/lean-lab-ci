/-
Elementary coefficient identities for P0069 page 11 before display 3.1.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165

namespace LeanLab.BHP1997.Decomp513a

/-- P0069 page 11, the critical line polynomial before display 3.1.
Factor the square root weight from the oscillatory logarithmic phase. -/
theorem critical_line_term (n : ℕ) (hn : 0 < (n : ℝ)) (a b : ℂ) (t : ℝ) :
    (a / (n : ℂ) ^ (1 / 2 : ℂ)) * b *
      Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I) =
      a * b / (n : ℂ) ^ Thm4.half t := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Complex.cpow_def_of_ne_zero hn0, div_eq_mul_inv,
    ← Complex.exp_neg, Thm4.half, ← Complex.natCast_log]
  calc
    _ = a * b * (Complex.exp (-(Real.log n : ℂ) * (1 / 2)) *
        Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)) := by
      push_cast
      ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- P0069 page 11, the coefficient energy of display 3.3.
The square norm of a coefficient divided by the square root of n is its norm square over n. -/
theorem critical_line_coefficient_norm_sq (n : ℕ) (hn : 0 < (n : ℝ)) (a : ℂ) :
    ‖a / (n : ℂ) ^ (1 / 2 : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / (n : ℝ) := by
  have hr : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = n := by
    rw [pow_two, ← Real.rpow_add hn]
    norm_num
  simp only [norm_div,
    Complex.norm_natCast_cpow_of_re_ne_zero n (by norm_num : (1 / 2 : ℂ).re ≠ 0)]
  rw [show (1 / 2 : ℂ).re = (1 : ℝ) / 2 by norm_num]
  rw [div_pow, hr]

end LeanLab.BHP1997.Decomp513a
