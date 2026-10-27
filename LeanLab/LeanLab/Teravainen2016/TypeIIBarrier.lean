/-
P0076 displays 11.5 and 11.6, page 46. The eighth root term explains the exponent 1/80.
This is a limitation of that bound, not a limitation theorem for the primes.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.TypeIISaving

namespace LeanLab.Teravainen2016

/-- At the allowed lower endpoint for Delta1, the eighth root term is at least N to minus 1/80. -/
theorem typeII_tail_lower {N : ℝ} (hN : 0 < N) :
    N ^ (-(1 : ℝ) / 80) ≤
      (1 / N ^ ((1 : ℝ) / 10) + 1 / N ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 8) := by
  have h : 1 / N ^ ((1 : ℝ) / 10) ≤
      1 / N ^ ((1 : ℝ) / 10) + 1 / N ^ ((1 : ℝ) / 2) := by
    have hh : 0 ≤ 1 / N ^ ((1 : ℝ) / 2) := by positivity
    linarith
  have hh := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have he : (1 / N ^ ((1 : ℝ) / 10)) ^ ((1 : ℝ) / 8) = N ^ (-(1 : ℝ) / 80) := by
    rw [one_div, ← Real.rpow_neg hN.le, ← Real.rpow_mul hN.le]
    congr 1
    norm_num
  rwa [he] at hh

/-- The bound cannot save a power when the frequency range reaches N to the power 1/80. -/
theorem typeII_kernel_ge_N {N M D₂ θ : ℝ} (hN : 1 ≤ N) (hM : 0 < M) (hθ : 1 / 80 ≤ θ) :
    N ≤ typeIIKernel N (N ^ θ) M (N ^ ((1 : ℝ) / 10)) D₂ := by
  have hN0 : 0 < N := by linarith
  have htail := typeII_tail_lower hN0
  have hfirst : 0 ≤
      (N ^ ((1 : ℝ) / 10) * M / N + N ^ ((1 : ℝ) / 10) * D₂ ^ 2 / M) ^ ((1 : ℝ) / 2) := by
    apply Real.rpow_nonneg
    positivity
  have hp : N ≤ N ^ (1 + θ - 1 / 80) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN (show (1 : ℝ) ≤ 1 + θ - 1 / 80 by linarith)
  calc
    _ ≤ N ^ (1 + θ - 1 / 80) := hp
    _ = N ^ θ * N * N ^ (-(1 : ℝ) / 80) := by
      rw [rpow_scale_cancel hN0]
      congr 1
      ring
    _ ≤ _ := by
      unfold typeIIKernel
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith

/-- A strict sublinear power bound fails for this admissible endpoint of the error expression. -/
theorem typeII_not_strict_power_saving {N M D₂ θ ε : ℝ} (hN : 1 < N) (hM : 0 < M)
    (hθ : 1 / 80 ≤ θ) (hε : 0 < ε) :
    ¬ typeIIKernel N (N ^ θ) M (N ^ ((1 : ℝ) / 10)) D₂ ≤ N ^ (1 - ε) := by
  have hl := typeII_kernel_ge_N (D₂ := D₂) hN.le hM hθ
  have hp : N ^ (1 - ε) < N := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hN (show 1 - ε < (1 : ℝ) by linarith)
  linarith

#print axioms typeII_tail_lower
#print axioms typeII_kernel_ge_N
#print axioms typeII_not_strict_power_saving

end LeanLab.Teravainen2016
