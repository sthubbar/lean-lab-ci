/-
P0059 arXiv 1407.7902v1 page 9 equation 3.1.
Journal INTEGERS 14 A61 page 12 equation 65.
The polynomial weight has mass 2^(2m) (m!)^2 / (2m+1)!.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.Weight

namespace LeanLab.KadiriLumley2014.Task64
open Real intervalIntegral

/-- The beta integral for nonnegative integer exponents. -/
theorem integral_nat_beta (m n : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ m * (1 - t) ^ n) =
      (m.factorial : ℝ) * n.factorial / (m + n + 1).factorial := by
  have hs : (0 : ℝ) < ((m : ℂ) + 1).re := by simp; positivity
  have ht : (0 : ℝ) < ((n : ℂ) + 1).re := by simp; positivity
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hs ht
  have heq : (m : ℂ) + 1 + ((n : ℂ) + 1) = ((m + n + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  rw [Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    heq, Complex.Gamma_nat_eq_factorial] at h
  have hb : Complex.betaIntegral ((m : ℂ) + 1) ((n : ℂ) + 1) =
      ((∫ t in (0 : ℝ)..1, t ^ m * (1 - t) ^ n : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    simp only [add_sub_cancel_right, Complex.cpow_natCast]
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    ext t
    push_cast
    rfl
  rw [hb] at h
  have hr : (m.factorial : ℝ) * n.factorial =
      (m + n + 1).factorial * (∫ t in (0 : ℝ)..1, t ^ m * (1 - t) ^ n) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using h
  have hf : ((m + n + 1).factorial : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hf).2
  linarith

/-- Exact mass formula used in Section 3.1. -/
theorem weight_mass (m : ℕ) :
    (∫ t in (0 : ℝ)..1, weight m t) =
      2 ^ (2 * m) * (m.factorial : ℝ) ^ 2 / (2 * m + 1).factorial := by
  have heq : (fun t : ℝ => weight m t) =
      (fun t => (4 : ℝ) ^ m * (t ^ m * (1 - t) ^ m)) := by
    ext t
    simp only [weight, mul_pow]
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_nat_beta]
  have hp : (4 : ℝ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  rw [hp]
  have hi : m + m + 1 = 2 * m + 1 := by omega
  rw [hi]
  ring

end LeanLab.KadiriLumley2014.Task64
