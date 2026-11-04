import LeanLab.ChirreHagen2025.TailIntegral297
import LeanLab.ChirreHagen2025.Decomp122b

/-!
An elementary pointwise component for P0075 Lemma 2.3, page 4.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Pointwise297

/-- P0075 page 4, elementary arithmetic for the inherited pointwise leaf.
The paper's logarithmic bound is much smaller than the linear majorant. -/
theorem four_log_sq_le_ten_mul {t : ℝ} (ht : 10 ^ 4 ≤ t) :
    (4 * Real.log t) ^ 2 ≤ 10 * t := by
  have ht0 : 0 < t := by norm_num at ht; linarith
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by norm_num at ht; linarith)
  have hlogbase : Real.log (10000 : ℝ) ≤ 36 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    have he : Real.log (10000 : ℝ) = 4 * Real.log 10 := by
      rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow]
      norm_num
    linarith
  have ha := Real.log_div_sqrt_antitoneOn
    (TailIntegral297.exp_two_lt_eight.le.trans (by norm_num : (8 : ℝ) ≤ 10000))
    (TailIntegral297.exp_two_lt_eight.le.trans (by norm_num at ht; linarith : (8 : ℝ) ≤ t))
    (show (10000 : ℝ) ≤ t by norm_num at ht; exact ht)
  norm_num at ha
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hlog : Real.log t ≤ (36 / 100) * Real.sqrt t := by
    apply (div_le_iff₀ hr).mp
    exact ha.trans (by nlinarith)
  have hs := mul_self_le_mul_self hl0 hlog
  nlinarith [Real.sq_sqrt ht0.le]

/-- P0075 page 4, the exact pointwise leaf of DecompJ932.
CONDITIONAL ON the OPEN Backlund leaves through lemma2_1_assembled. -/
theorem leaf_integrand_bound : RiemannHypothesis → ∀ t : ℝ, 10 ^ 4 ≤ t →
    ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)‖ ^ 2
    ≤ 10 * t := by
  intro hRH t ht
  have ht100 : 100 ≤ |t| := by norm_num at ht; rw [abs_of_nonneg (by linarith)]; linarith
  have h := Decomp122b.lemma2_1_assembled hRH 1 t le_rfl (by norm_num) ht100
  rw [abs_of_nonneg (by norm_num at ht; linarith)] at h
  have hn := norm_nonneg (deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I))
  calc
    _ ≤ (4 * Real.log t) ^ 2 := by simpa only [pow_two] using mul_self_le_mul_self hn h
    _ ≤ 10 * t := four_log_sq_le_ten_mul ht

end LeanLab.ChirreHagen2025.Pointwise297
