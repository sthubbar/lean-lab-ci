/-
Jia 1996 pages 270, 275 and 281, supporting Lemmas 24 to 27.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
These are elementary integrand identities, not prime distribution estimates.
-/
import LeanLab.Languasco2004.BuchstabInitial316

namespace LeanLab.Languasco2004.Kernel548
open Real BuchstabInitial316
noncomputable section

/-- Pages 270 and 275: the first Buchstab formula gives the rational kernel. -/
theorem initial_kernel_low (t u : ℝ) (ht : 0 < t) (hu : 0 < u)
    (hv : 0 < 1 - t - u) (hs : (1 - t - u) / u ≤ 2) :
    buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) =
      1 / (t * u * (1 - t - u)) := by
  rw [buchstabInitial_eq_inv hs]
  field_simp

/-- Pages 270 and 281: the second Buchstab formula gives the logarithmic kernel. -/
theorem initial_kernel_high (t u : ℝ) (ht : 0 < t) (hu : 0 < u)
    (hv : 0 < 1 - t - u) (hs : 2 ≤ (1 - t - u) / u) :
    buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) =
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  rw [buchstabInitial_eq_log hs]
  have heq : (1 - t - u) / u - 1 = (1 - t) / u - 2 := by
    field_simp
    ring
  rw [heq]
  field_simp

/-- Page 275: throughout D47 the Buchstab argument is between one and two. -/
theorem region47_argument (t u : ℝ) (htl : 11 / 27 ≤ t) (htu : t ≤ 34 / 81)
    (hul : 17 / 12 - 23 / 8 * t ≤ u) (huu : u ≤ 25 / 72 - t / 4) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧
      1 ≤ (1 - t - u) / u ∧ (1 - t - u) / u ≤ 2 := by
  have ht : 0 < t := by linarith
  have hu : 0 < u := by linarith
  refine ⟨ht, hu, by linarith, ?_, ?_⟩
  · apply (le_div_iff₀ hu).mpr
    linarith
  · apply (div_le_iff₀ hu).mpr
    linarith

/-- Page 281: throughout D30 the Buchstab argument is between two and three. -/
theorem region30_argument (t u : ℝ) (htl : 34 / 99 ≤ t) (htu : t ≤ 1649 / 4752)
    (hul : 85 / 99 - 2 * t ≤ u) (huu : u ≤ 85 / 147 - 58 / 49 * t) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧
      2 ≤ (1 - t - u) / u ∧ (1 - t - u) / u ≤ 3 := by
  have ht : 0 < t := by linarith
  have hu : 0 < u := by linarith
  refine ⟨ht, hu, by linarith, ?_, ?_⟩
  · apply (le_div_iff₀ hu).mpr
    linarith
  · apply (div_le_iff₀ hu).mpr
    linarith

/-- Page 275: the complete first integral for Omega47 has the rational kernel. -/
theorem region47_kernel (t u : ℝ) (htl : 11 / 27 ≤ t) (htu : t ≤ 34 / 81)
    (hul : 17 / 12 - 23 / 8 * t ≤ u) (huu : u ≤ 25 / 72 - t / 4) :
    buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) =
      1 / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, _, hs⟩ := region47_argument t u htl htu hul huu
  exact initial_kernel_low t u ht hu hv hs

/-- Page 281: the complete first integral for Omega30 has the logarithmic kernel. -/
theorem region30_kernel (t u : ℝ) (htl : 34 / 99 ≤ t) (htu : t ≤ 1649 / 4752)
    (hul : 85 / 99 - 2 * t ≤ u) (huu : u ≤ 85 / 147 - 58 / 49 * t) :
    buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) =
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, hs, _⟩ := region30_argument t u htl htu hul huu
  exact initial_kernel_high t u ht hu hv hs

#print axioms initial_kernel_low
#print axioms initial_kernel_high
#print axioms region47_argument
#print axioms region30_argument
#print axioms region47_kernel
#print axioms region30_kernel
end
end LeanLab.Languasco2004.Kernel548
