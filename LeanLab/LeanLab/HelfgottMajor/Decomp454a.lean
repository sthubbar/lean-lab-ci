import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The retained boundary in the decreasing error calculation of P0014 page 38.
Display 4.35 on page 41 uses that calculation to obtain countDensity.
These identities audit that step and do not refute the sealed tail_mass_integral.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454a
open MeasureTheory Real Set Filter
open scoped Topology

/-- Exact integration by parts for the error expression after P0014 display 4.28.
The endpoint occurs twice in the expression with minus the derivative integral.
This is a derived correction to the printed calculation on page 38.
-/
theorem error_boundary_identity (f f' g g' : ℝ → ℝ) (y : ℝ)
    (hf : ∀ t ∈ Ioi y, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Ioi y, HasDerivAt g (g' t) t)
    (hfg' : IntegrableOn (fun t => f t * g' t) (Ioi y))
    (hf'g : IntegrableOn (fun t => f' t * g t) (Ioi y))
    (hstart : Tendsto (fun t => f t * g t) (𝓝[>] y) (𝓝 (f y * g y)))
    (hend : Tendsto (fun t => f t * g t) atTop (𝓝 0)) :
    f y * g y - (∫ t in Ioi y, f' t * g t) =
      2 * f y * g y + ∫ t in Ioi y, f t * g' t := by
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hf hg hfg' hf'g hstart hend
  linarith

/-- The exact retained boundary for the logarithmic envelope in P0014 display 4.25.
This is the corrected decreasing calculation after display 4.28 on page 38.
-/
theorem logarithmic_error_boundary (f f' : ℝ → ℝ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y)
    (hf : ∀ t ∈ Ioi y, HasDerivAt f (f' t) t)
    (hft : IntegrableOn (fun t => f t / t) (Ioi y))
    (hfg : IntegrableOn (fun t => f' t * (0.5 * log (q * t) + 17.7)) (Ioi y))
    (hstart : Tendsto (fun t => f t * (0.5 * log (q * t) + 17.7))
      (𝓝[>] y) (𝓝 (f y * (0.5 * log (q * y) + 17.7))))
    (hend : Tendsto (fun t => f t * (0.5 * log (q * t) + 17.7)) atTop (𝓝 0)) :
    f y * (0.5 * log (q * y) + 17.7) -
        (∫ t in Ioi y, f' t * (0.5 * log (q * t) + 17.7)) =
      2 * f y * (0.5 * log (q * y) + 17.7) +
        0.5 * ∫ t in Ioi y, f t / t := by
  have hg : ∀ t ∈ Ioi y,
      HasDerivAt (fun t => 0.5 * log (q * t) + 17.7) (0.5 / t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hy.trans ht)
    have h := (((hasDerivAt_id t).const_mul q).log
      (mul_ne_zero hq.ne' ht0)).const_mul (0.5 : ℝ)
    have heq : 0.5 * (q * 1 / (q * t)) = 0.5 / t := by
      field_simp
    simpa only [id_eq, heq] using h.add_const 17.7
  have hi : IntegrableOn (fun t => f t * (0.5 / t)) (Ioi y) := by
    have he : (fun t => f t * (0.5 / t)) = (fun t => 0.5 * (f t / t)) := by
      funext t
      ring
    rw [he]
    exact hft.const_mul (0.5 : ℝ)
  have h := error_boundary_identity f f' (fun t => 0.5 * log (q * t) + 17.7)
    (fun t => 0.5 / t) y hf hg hi hfg hstart hend
  have heq : (∫ t in Ioi y, f t * (0.5 / t)) =
      0.5 * ∫ t in Ioi y, f t / t := by
    rw [← integral_const_mul]
    congr 1
    ext t
    ring
  simpa only [heq] using h

/-- A corrected consequence of the partial summation error in P0014 display 4.27.
CONDITIONAL ON herr, the explicit partial summation error estimate.
The endpoint remains in the budget on page 38 and cannot be discarded in display 4.35.
-/
theorem partial_summation_error_bound (f f' g g' : ℝ → ℝ) (y S M : ℝ)
    (hf : ∀ t ∈ Ioi y, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Ioi y, HasDerivAt g (g' t) t)
    (hfg' : IntegrableOn (fun t => f t * g' t) (Ioi y))
    (hf'g : IntegrableOn (fun t => f' t * g t) (Ioi y))
    (hstart : Tendsto (fun t => f t * g t) (𝓝[>] y) (𝓝 (f y * g y)))
    (hend : Tendsto (fun t => f t * g t) atTop (𝓝 0))
    (herr : |S - M| ≤ (1 / 2 : ℝ) *
      (f y * g y - ∫ t in Ioi y, f' t * g t)) :
    S ≤ M + f y * g y + (1 / 2 : ℝ) * ∫ t in Ioi y, f t * g' t := by
  rw [error_boundary_identity f f' g g' y hf hg hfg' hf'g hstart hend] at herr
  linarith [(le_abs_self (S - M)).trans herr]

end LeanLab.HelfgottMajor.Decomp454a
