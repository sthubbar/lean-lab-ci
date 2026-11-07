/-
Split of the outer frequency square integrability `outer_kernel_mass_integrable442`.

The target asks that the square of the absolute log weighted Mellin kernel mass be
interval integrable in the frequency over the outer interval from 4 over N to 1 over R.
That is a compactness statement about a parametric integral, and it is proved here in
three steps.

Step 1 dominates the line integrand by one integrable function of the line variable,
uniformly over the whole outer frequency interval. The real part of the shifted line is
fixed, the base has real part 1 over N and the frequency is at least 4 over N, so the
ratio of the imaginary part of the base to its real part stays at least 8 pi and the
Gamma decay against the exponential of the complex power leaves an integrable weight.
Step 2 and step 3 record the two continuities the parametric integral needs: in the
frequency at fixed line point, and along the line at fixed frequency, the second giving
measurability in the line variable.

Nothing here changes the sealed statement: `outer_kernel_mass_integrable442_split`
restates the target character for character and derives it from the three leaves
without using the original theorem.
-/
import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Step 1 of 3: the line integrand of the absolute kernel mass is dominated by
one integrable function of the line variable, uniformly over the whole outer frequency
interval. The base of the complex power always has real part 1 over N, and its
imaginary part is at least 8 pi times its real part, so the exponential of the power
loses a fixed positive fraction of the Gamma decay and the logarithmic weight cubed is
absorbed. No coefficient occurs. -/
theorem outer_kernel_weight_dominated442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    ∃ g : ℝ → ℝ, (∀ t : ℝ, 0 ≤ g t) ∧ Integrable g ∧
      ∀ α : ℝ, α ∈ Set.uIcc (4 / (N : ℝ)) (1 / R) → ∀ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤ g t := by
  sorry

/-- LEAF. Step 2 of 3: at a fixed line point the absolute kernel weight, logarithmic
factor included, is continuous in the frequency. The base stays in the open right half
plane because its real part is 1 over N, so the complex power is continuous there and
the Gamma factor and the logarithmic weight do not depend on the frequency. -/
theorem outer_kernel_weight_continuous_alpha442 (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    Continuous (fun α : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  sorry

/-- LEAF. Step 3 of 3: at a fixed frequency the absolute kernel weight is continuous
along the line. The line is the vertical line of real part 1 over 2 plus 1 over log N,
which avoids the poles of the Gamma factor, and the complex power is continuous in its
exponent because the base has positive real part. This is the measurability input of
the parametric integral. -/
theorem outer_kernel_weight_continuous_line442 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    Continuous (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  sorry

/-- Assembly from the three leaves. Step 1 gives the dominating integrable function,
step 3 makes each frequency slice measurable, step 2 gives continuity in the frequency,
so the mass is continuous on the compact outer interval; its square is then interval
integrable there. -/
theorem outer_kernel_mass_integrable442_split (N : ℕ) (hN : 3 ≤ N) (R : ℝ)
    (hR : 1 ≤ R) (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    IntervalIntegrable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) volume
      (4 / (N : ℝ)) (1 / R) := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨g, hg0, hgint, hgb⟩ := outer_kernel_weight_dominated442 N hN R hR hR2
  have hmeas : ∀ α ∈ Set.uIcc (4 / (N : ℝ)) (1 / R),
      AEStronglyMeasurable (fun t : ℝ => ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) volume :=
    fun α _ => (outer_kernel_weight_continuous_line442 N hN1 α).aestronglyMeasurable
  have hbound : ∀ α ∈ Set.uIcc (4 / (N : ℝ)) (1 / R),
      ∀ᵐ t ∂volume, ‖‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3‖ ≤ g t := by
    intro α hα
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h0 : 0 ≤ ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h1 : (1 : ℝ) < (N : ℝ) * (|t| + 2) := by
        nlinarith [abs_nonneg t]
      have h2 : 0 < Real.log ((N : ℝ) * (|t| + 2)) := Real.log_pos h1
      exact mul_nonneg (norm_nonneg _) (pow_pos h2 3).le
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hgb α hα t
  have hcont : ContinuousOn (fun α : ℝ =>
      ∫ t : ℝ, ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) (Set.uIcc (4 / (N : ℝ)) (1 / R)) :=
    continuousOn_of_dominated hmeas hbound hgint
      (Filter.Eventually.of_forall
        (fun t => (outer_kernel_weight_continuous_alpha442 N hN1 t).continuousOn))
  exact (hcont.pow 2).intervalIntegrable

end LeanLab.Linnik1951
