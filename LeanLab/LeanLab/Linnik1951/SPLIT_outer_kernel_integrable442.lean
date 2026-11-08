/-
Split of the abstract outer Mellin kernel estimate `outer_kernel_integrable442`
into four steps plus one assembly.

The estimate is one integrability claim about the absolute value of the outer
Mellin kernel on the shifted line, weighted by the cube of the logarithm. The
kernel factor is a complex power of a fixed nonzero base times the Gamma
function; along the line the Gamma factor decays exponentially in the absolute
imaginary part, and the logarithm weight grows only cubically, so the weighted
kernel is dominated by an exponentially decaying cubic. The split records that
argument in four pieces: the exponential decay of the kernel factor with
constants that may depend on the parameters, the cubic polynomial bound on the
logarithm weight, the integrability of the exponential decay times the cubic,
and the strong measurability of the weighted kernel. The assembly below
combines them through the dominated convergence inequality for the Bochner
integral.

Nothing here changes the statement of `outer_kernel_integrable442`; the theorem
`outer_kernel_integrable442_split` restates it character for character and
proves it from the four leaves without using the original theorem.
-/
import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Step 1 of 4: exponential decay of the kernel factor in the variable of
integration. For N at least three and a frequency in the outer interval, the
complex power and the Gamma factor together are dominated by one exponential
with a positive rate, the two constants depending on N, R and the frequency but
not on the integration variable. No logarithm weight and no coefficient
occurs. -/
theorem outer_kernel_decay442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (α : ℝ) (hα : α ∈ Set.Icc (4 / (N : ℝ)) (1 / R)) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ t : ℝ,
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ ≤
        K * Real.exp (-(δ * |t|)) := by
  sorry

/-- LEAF. Step 2 of 4: the cube of the logarithm weight is bounded by a cubic
polynomial in the absolute value of the integration variable. The constant
depends on N only, and there is no kernel factor here. -/
theorem log_weight_cubic442 (N : ℕ) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤ C * (1 + |t|) ^ 3 := by
  sorry

/-- LEAF. Step 3 of 4: for every positive rate the exponential decay times the
cubic polynomial is integrable on the line. This is the model estimate that the
dominating function has to satisfy, and it carries no kernel, no Gamma factor
and no logarithm of N. -/
theorem exp_decay_cubic_integrable442 :
    ∀ δ : ℝ, 0 < δ → Integrable (fun t : ℝ =>
      Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) := by
  sorry

/-- LEAF. Step 4 of 4: strong measurability of the log weighted kernel. The base
is a fixed nonzero complex number, the line is continuous in the variable of
integration and the Gamma factor is continuous on the half plane of positive
real part, which is where the shifted line lies. This is the measurability half
of the conclusion, without any bound. -/
theorem outer_kernel_aestronglyMeasurable442 (N : ℕ) (R : ℝ) (α : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  sorry

/-- Assembly of `outer_kernel_integrable442` from the four leaves. The decay
constants and the polynomial constant of the two bounds multiply into the
dominating exponential times cubic, which is integrable by the model estimate,
and the weighted kernel is measurable, so the dominated convergence inequality
for the Bochner integral gives the conclusion. -/
theorem outer_kernel_integrable442_split (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (α : ℝ) (hα : α ∈ Set.Icc (4 / (N : ℝ)) (1 / R)) :
    Integrable (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  obtain ⟨K, δ, hK, hδ, hdec⟩ := outer_kernel_decay442 N hN R hR α hα
  obtain ⟨C, hC, hlog⟩ := log_weight_cubic442 N hN
  have hint : Integrable (fun t : ℝ =>
      K * C * (Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3)) :=
    (exp_decay_cubic_integrable442 δ hδ).const_mul (K * C)
  refine hint.mono' (outer_kernel_aestronglyMeasurable442 N R α)
    (Filter.Eventually.of_forall (fun t => ?_))
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
    apply Real.log_nonneg
    nlinarith [abs_nonneg t]
  have hfnn : (0 : ℝ) ≤
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
    mul_nonneg (norm_nonneg _) (pow_nonneg hlog0 3)
  have hpoly : (0 : ℝ) ≤ (1 + |t|) ^ 3 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  calc
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3
        ≤ ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            (C * (1 + |t|) ^ 3) :=
          mul_le_mul_of_nonneg_left (hlog t) (norm_nonneg _)
    _ = (‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ * C) *
            (1 + |t|) ^ 3 := by ring
    _ ≤ ((K * Real.exp (-(δ * |t|))) * C) * (1 + |t|) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hdec t) hC.le) hpoly
    _ = K * C * (Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) := by ring

end LeanLab.Linnik1951
