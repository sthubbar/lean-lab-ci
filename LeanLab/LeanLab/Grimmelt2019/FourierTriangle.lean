/-
AI wrote this Lean code for CODEX task03.
P0074, page 12, the triangle argument in Corollary 4.3.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Prop21

namespace LeanLab.Grimmelt2019.Prop21
open Real
attribute [local instance] Classical.propDecidable

/-- The finite Fourier series is additive in the sequence. -/
theorem fhat_add (S : Finset ℤ) (f g : ℤ → ℝ) (α : ℝ) :
    fhat S (fun n => f n + g n) α = fhat S f α + fhat S g α := by
  unfold fhat
  simp_rw [Complex.ofReal_add, add_mul]
  exact Finset.sum_add_distrib

/-- A finite Fourier series is continuous. -/
@[fun_prop] theorem continuous_fhat (S : Finset ℤ) (f : ℤ → ℝ) : Continuous (fhat S f) := by
  unfold fhat
  fun_prop

/-- Its squared norm on any translated finite interval is integrable. -/
theorem fhat_sq_intervalIntegrable (S : Finset ℤ) (f : ℤ → ℝ) (α a b : ℝ) :
    IntervalIntegrable (fun β => ‖fhat S f (α + β)‖ ^ 2) MeasureTheory.volume a b := by
  have hc : Continuous (fun β => ‖fhat S f (α + β)‖ ^ 2) := by fun_prop
  exact hc.intervalIntegrable _ _

/-- Adding two Fourier-close errors costs at most twice the sum of their squared bounds. -/
theorem fourierClose_add {S : Finset ℤ} {f g : ℤ → ℝ} {H Δf Δg : ℝ}
    (hH : 0 ≤ H) (hf : FourierClose S H Δf f) (hg : FourierClose S H Δg g) :
    FourierClose S H (2 * Δf + 2 * Δg) (fun n => f n + g n) := by
  intro α
  have hI : -(1 / H) ≤ 1 / H := by
    have hnonneg : 0 ≤ 1 / H := by positivity
    linarith
  have hfi := fhat_sq_intervalIntegrable S f α (-(1 / H)) (1 / H)
  have hgi := fhat_sq_intervalIntegrable S g α (-(1 / H)) (1 / H)
  have hsum := fhat_sq_intervalIntegrable S (fun n => f n + g n) α (-(1 / H)) (1 / H)
  have hright := (hfi.const_mul 2).add (hgi.const_mul 2)
  have hmono := intervalIntegral.integral_mono hI hsum hright (fun β => ?_)
  · rw [intervalIntegral.integral_add (hfi.const_mul 2) (hgi.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (by linarith [hf α, hg α])
  · rw [fhat_add]
    calc
      ‖fhat S f (α + β) + fhat S g (α + β)‖ ^ 2 ≤
          (‖fhat S f (α + β)‖ + ‖fhat S g (α + β)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ ≤ _ := by nlinarith [sq_nonneg (‖fhat S f (α + β)‖ - ‖fhat S g (α + β)‖)]

/-- Corollary 4.3 follows from the two Fourier closeness bounds with an explicit factor four. -/
theorem cor43_of_two_bounds {S : Finset ℤ} {ν T Tp : ℤ → ℝ} {H Δ : ℝ}
    (hH : 0 ≤ H) (h33 : FourierClose S H Δ (fun n => ν n - T n))
    (h42 : FourierClose S H Δ (fun n => T n - Tp n)) :
    FourierClose S H (4 * Δ) (fun n => ν n - Tp n) := by
  have h := fourierClose_add hH h33 h42
  convert h using 1 <;> (first | funext n; ring | ring)

#print axioms fhat_add
#print axioms continuous_fhat
#print axioms fhat_sq_intervalIntegrable
#print axioms fourierClose_add
#print axioms cor43_of_two_bounds
end LeanLab.Grimmelt2019.Prop21
