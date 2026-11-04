/-
P0059 arXiv 1407.7902v1 page 6 before equations 2.34 to 2.39.
Conjugation symmetry of the polynomial smoothing factor.
AI wrote this Lean code. CODEX task301. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.G92

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory
open scoped ComplexConjugate
open Task64 Task92

/-- The weight transform commutes with conjugation for nonnegative delta. -/
theorem weightTransform_conj (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (s : ℂ) :
    weightTransform m δ (conj s) = conj (weightTransform m δ s) := by
  unfold weightTransform
  rw [map_div₀, Complex.conj_ofReal, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have hb : 0 < 1 + δ * t := by nlinarith [ht.1]
  have harg : (((1 + δ * t : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hb.le]
    exact Real.pi_ne_zero.symm
  dsimp only
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal, map_mul, Complex.conj_ofReal]

/-- G commutes with conjugation, including at zero u under Lean total division. -/
theorem smoothingG_conj (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) (s : ℂ) :
    smoothingG m δ u (conj s) = conj (smoothingG m δ u s) := by
  have he : Complex.exp (conj s * (u : ℂ)) = conj (Complex.exp (s * u)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  unfold smoothingG
  rw [weightTransform_conj m hδ s, he]
  simp [-Complex.ofReal_exp]

/-- The two G norms in the conjugate pair are equal. -/
theorem smoothingG_norm_conj (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) (s : ℂ) :
    ‖smoothingG m δ u (conj s)‖ = ‖smoothingG m δ u s‖ := by
  rw [smoothingG_conj m hδ u s, Complex.norm_conj]

/-- The paired transform defined on page 6 is exactly twice the single G norm. -/
theorem smoothingG_pair_eq_two (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) (s : ℂ) :
    ‖smoothingG m δ u s‖ + ‖smoothingG m δ u (conj s)‖ = 2 * ‖smoothingG m δ u s‖ := by
  rw [smoothingG_norm_conj m hδ u s]
  ring

end LeanLab.KadiriLumley2014.Task301
