/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362a

namespace LeanLab.Tchudakov1938.Decomp362h
open Complex MeasureTheory

/-- LEAF. P0064, page 33, first display in the Lemma 11 proof. The square-difference estimate holds with constant two. -/
theorem square_difference (z w : ℂ) : ‖z^2 - w^2‖^2 ≤ 2 * ‖z-w‖^2 * (‖z‖^2 + ‖w‖^2) := by
  have heq : z^2 - w^2 = (z - w) * (z + w) := by ring
  rw [heq, norm_mul, mul_pow]
  have h := norm_add_le z w
  have hs : ‖z+w‖^2 ≤ 2 * (‖z‖^2 + ‖w‖^2) := by
    nlinarith [norm_nonneg (z+w), norm_nonneg z, norm_nonneg w, sq_nonneg (‖z‖ - ‖w‖)]
  calc
    _ ≤ ‖z-w‖^2 * (2 * (‖z‖^2 + ‖w‖^2)) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- LEAF. P0064, page 32, the phase-increment estimate before inequality 17. Reuse the Mathlib imaginary-exponential bound. -/
theorem phase_increment (m θ : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * m * θ)) -
      Complex.exp (Complex.I * (2 * Real.pi * (m + 1) * θ))‖ ≤ 2 * Real.pi * |θ| := by
  have heq : Complex.exp (Complex.I * (2 * Real.pi * (m + 1) * θ)) =
      Complex.exp (Complex.I * (2 * Real.pi * m * θ)) * Complex.exp (Complex.I * (2 * Real.pi * θ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [heq]
  nth_rw 1 [← mul_one (Complex.exp (Complex.I * (2 * Real.pi * m * θ)))]
  rw [← mul_sub, norm_mul]
  have hn : ‖Complex.exp (Complex.I * (2 * Real.pi * m * θ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hn, one_mul, norm_sub_rev]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * θ)
  push_cast at h
  calc
    _ ≤ ‖(2 * Real.pi * θ : ℝ)‖ := h
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)]


/-- CONDITIONAL ON the pointwise major-arc approximation and integrability. P0064, page 33, inequality 21, first integral bound. This is the analytic transfer step for the functions restricted to one measurable arc. -/
theorem square_difference_integral (S ψ : ℝ → ℂ) (E : ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hS : IntegrableOn (fun x => ‖S x‖^2) s) (hψ : IntegrableOn (fun x => ‖ψ x‖^2) s)
    (hF : IntegrableOn (fun x => ‖(S x)^2 - (ψ x)^2‖^2) s)
    (hD : ∀ x ∈ s, ‖S x - ψ x‖ ≤ E) :
    (∫ x in s, ‖(S x)^2 - (ψ x)^2‖^2) ≤
      2 * E^2 * ((∫ x in s, ‖S x‖^2) + ∫ x in s, ‖ψ x‖^2) := by
  have hbound : ∀ x ∈ s, ‖(S x)^2 - (ψ x)^2‖^2 ≤ 2 * E^2 * (‖S x‖^2 + ‖ψ x‖^2) := by
    intro x hx
    have hd := pow_le_pow_left₀ (norm_nonneg (S x - ψ x)) (hD x hx) 2
    exact (square_difference (S x) (ψ x)).trans (by gcongr)
  calc
    (∫ x in s, ‖(S x)^2 - (ψ x)^2‖^2) ≤ ∫ x in s, 2 * E^2 * (‖S x‖^2 + ‖ψ x‖^2) := by
      apply integral_mono_ae hF ((hS.add hψ).const_mul (2 * E^2))
      filter_upwards [ae_restrict_mem hs] with x hx
      exact hbound x hx
    _ = _ := by rw [integral_const_mul, integral_add hS hψ]

end LeanLab.Tchudakov1938.Decomp362h
