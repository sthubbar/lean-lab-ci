/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Period and sign conventions for Lemma 3.3, page 356.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ModelIntegral

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology LeanLab.CircleOrth MeasureTheory

theorem ee_integer (k : ℤ) : ee k = 1 := by
  unfold ee
  convert Complex.exp_int_mul_two_pi_mul_I k using 1 <;> push_cast <;> ring

theorem ee_frequency_periodic (k : ℤ) :
    Function.Periodic (fun α : ℝ => ee (k * α)) 1 := by
  intro α
  change ee ((k : ℝ) * (α + 1)) = ee ((k : ℝ) * α)
  rw [mul_add, ee_add, mul_one, ee_integer, mul_one]

theorem modelSum_periodic (N : ℕ) : Function.Periodic (modelSum N) 1 := by
  intro α
  unfold modelSum
  apply tsum_congr
  intro n
  rw [show (n : ℝ) * (α + 1) = n * α + n by ring, ee_add]
  have hn : ee (n : ℝ) = 1 := by exact_mod_cast ee_integer (n : ℤ)
  rw [hn, mul_one]

theorem modelIntegrand_periodic (N : ℕ) :
    Function.Periodic (fun α : ℝ => modelSum N α ^ 3 * ee (-((N : ℤ) * α))) 1 := by
  have h : Function.Periodic (fun α : ℝ => ee (-((N : ℤ) * α))) 1 := by
    simpa only [Int.cast_neg, neg_mul] using ee_frequency_periodic (-(N : ℤ))
  intro α
  change modelSum N (α + 1) ^ 3 * ee (-((N : ℤ) * (α + 1))) = _
  have he : ee (-((N : ℤ) * (α + 1))) = ee (-((N : ℤ) * α)) := h α
  rw [modelSum_periodic N α, he]

/-- The model integral is unchanged by moving the full period to the paper's interval. -/
theorem modelIntegral_centered (N : ℕ) :
    modelIntegral N = ∫ α in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      modelSum N α ^ 3 * ee (-((N : ℤ) * α)) := by
  have h := (modelIntegrand_periodic N).intervalIntegral_add_eq 0 (-1 / 2)
  norm_num only [zero_add, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
  simpa only [modelIntegral, neg_div] using h

/-- Reflection recovers the Fourier signs in the paper. -/
theorem modelIntegral_paper_sign (N : ℕ) :
    (∫ α in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      modelSum N (-α) ^ 3 * ee ((N : ℤ) * α)) = modelIntegral N := by
  rw [modelIntegral_centered]
  have h := intervalIntegral.integral_comp_neg
    (f := fun α : ℝ => modelSum N α ^ 3 * ee (-((N : ℤ) * α)))
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  norm_num only [neg_div, neg_neg] at h
  simpa only [mul_neg, neg_neg, neg_div] using h

/-- Lemma 3.3 with the paper's interval and Fourier signs and the factor from its proof. -/
theorem lemma33_integral (N : ℕ) (hN : 8 ≤ N) :
    (∫ α in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      modelSum N (-α) ^ 3 * ee ((N : ℤ) * α)) =
      ((((N : ℝ) - 8) * ((N : ℝ) - 7) / 2 / Real.exp 1 : ℝ) : ℂ) := by
  rw [modelIntegral_paper_sign, modelIntegral_eq_polynomial N hN]

end LeanLab.Zinoviev1997
