/-
P0093 page 156 equation 4.1. Nonzero central kernel and coefficient witnesses.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp442a

namespace LeanLab.Linnik1951

/-- P0093 page 156 equation 4.1. For N greater than one the Mellin
kernel has positive norm at every real phase and frequency. Its base
has positive real part and its Gamma argument has positive real part. -/
theorem mellin_kernel_norm_pos442 (N : ℕ) (hN : 1 < N) (α t : ℝ) :
    0 < ‖mellinKernel442 N α t‖ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  apply norm_pos_iff.mpr
  apply mul_ne_zero
  · apply Complex.cpow_ne_zero_iff.mpr
    apply Or.inl
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    exact (ne_of_gt (one_div_pos.mpr hNp)) hre
  · apply Complex.Gamma_ne_zero_of_re_pos
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    positivity

/-- P0093 page 156 equation 4.1. The constant one coefficient
satisfies the line bound at every N at least three. This supplies a
nonzero witness arbitrarily far beyond any threshold. -/
theorem lineBound_one_large442 (N : ℕ) (hN : 3 ≤ N) :
    LineBound1622 N 1 (fun _ => 1) := by
  refine ⟨continuous_const, fun t => ?_⟩
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : Real.exp 1 ≤ (N : ℝ) * (|t| + 2) := by
    nlinarith [abs_nonneg t, Real.exp_one_lt_three]
  have hl := Real.log_le_log (Real.exp_pos 1) hx
  rw [Real.log_exp] at hl
  simpa using one_le_pow₀ hl (n := 3)

end LeanLab.Linnik1951
