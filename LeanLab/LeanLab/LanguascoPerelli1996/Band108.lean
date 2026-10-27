import LeanLab.LanguascoPerelli1996.Zeros108
import LeanLab.LanguascoPerelli1996.Sobolev108

/-!
Regularity of the zero band sums used in P0071 page 355 displays 12 and 13.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Band108
open Real
open scoped ContDiff

/-- Page 354. The zero band sum is an actual finite sum for every height. -/
theorem zSum_eq_sum (y U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) :
    zSum y U T q a =
      ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
        ∑ ρ ∈ ((Zeros108.ntZeros_finite χ T).sdiff (t := {ρ | |ρ.im| ≤ U})).toFinset,
          (mult χ ρ : ℂ) * Complex.exp (Complex.I * (ρ.im : ℂ) * (Real.log y : ℂ)) := by
  classical
  unfold zSum
  congr 1
  ext χ
  rw [finsum_mem_eq_finite_toFinset_sum _ ((Zeros108.ntZeros_finite χ T).sdiff (t := {ρ | |ρ.im| ≤ U}))]

/-- LEAF. Page 354 definition of G and page 355 display 12.
The zero band sum at X exp v is smooth in the real variable v. -/
theorem band_contDiff {X : ℝ} (hX : 0 < X) (U T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    ContDiff ℝ ∞ (fun v : ℝ => zSum (X * Real.exp v) U T q a) := by
  classical
  have heq : (fun v : ℝ => zSum (X * Real.exp v) U T q a) =
      (fun v : ℝ => ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
        ∑ ρ ∈ ((Zeros108.ntZeros_finite χ T).sdiff (t := {ρ | |ρ.im| ≤ U})).toFinset,
          (mult χ ρ : ℂ) * Complex.exp (Complex.I * (ρ.im : ℂ) * ((Real.log X + v : ℝ) : ℂ))) := by
    funext v
    rw [zSum_eq_sum]
    simp only [Real.log_mul hX.ne' (Real.exp_pos v).ne', Real.log_exp]
  rw [heq]
  have hcast : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

/-- LEAF. Page 354 definition of G. The squared norm of the band sum is smooth. -/
theorem energy_contDiff {X : ℝ} (hX : 0 < X) (U T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    ContDiff ℝ ∞ (fun v : ℝ => ‖zSum (X * Real.exp v) U T q a‖ ^ 2) := by
  exact (band_contDiff hX U T q a).norm_sq ℂ

/-- LEAF. Page 355 display 12, Sobolev applied to the actual zero band energy. -/
theorem band_sobolev {X : ℝ} (hX : 0 < X) (U T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    ‖zSum X U T q a‖ ^ 2 ≤
      (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) +
      ∫ v in (-1 : ℝ)..1, |deriv (fun t : ℝ => ‖zSum (X * Real.exp t) U T q a‖ ^ 2) v| := by
  have hc := energy_contDiff hX U T q a
  have hh := Sobolev108.point_le_mass_add_variation hc.continuous
    (hc.continuous_deriv (by simp))
    (fun v => (hc.differentiable (by simp) v).hasDerivAt) (fun v => sq_nonneg _)
  simpa only [Real.exp_zero, mul_one] using hh

end LeanLab.LanguascoPerelli1996.Band108
