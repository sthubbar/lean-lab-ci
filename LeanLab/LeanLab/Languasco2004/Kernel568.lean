/-
Jia 1996 page 279, Lemma 26 after displays 53 to 56.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Numeric30_548
namespace LeanLab.Languasco2004.Kernel568
open Real Numeric30_548 Kernel548 BuchstabInitial316
noncomputable section
/-- Page 279: the full closed Omega4 domain uses the second initial formula. -/
theorem region4_argument (t u : ℝ) (htl : 41 / 180 ≤ t) (htu : t ≤ 8 / 33)
    (hul : 41 / 90 - t ≤ u) (huu : u ≤ t) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧
      2 ≤ (1 - t - u) / u ∧ (1 - t - u) / u ≤ 3 := by
  have ht : 0 < t := by linarith
  have hu : 0 < u := by linarith
  refine ⟨ht, hu, by linarith, ?_, ?_⟩
  · apply (le_div_iff₀ hu).mpr
    linarith
  · apply (div_le_iff₀ hu).mpr
    linarith
/-- Page 279: the complete Omega4 Buchstab integral has the printed logarithmic kernel. -/
theorem region4_kernel (t u : ℝ) (htl : 41 / 180 ≤ t) (htu : t ≤ 8 / 33)
    (hul : 41 / 90 - t ≤ u) (huu : u ≤ t) :
    buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) =
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, hs, _⟩ := region4_argument t u htl htu hul huu
  exact initial_kernel_high t u ht hu hv hs
/-- Page 279 numerical support: Mathlib's first three positive series terms bound the logarithm. -/
theorem log_three_terms (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) :
    2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 ≤ Real.log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz hz1 3
  norm_num [Finset.sum_range_succ] at h
  linarith
/-- Page 279 numerical support: a polynomial minorant of the full Omega4 kernel. -/
def polynomial4 (t u : ℝ) : ℝ :=
  let v := invPoly3 (1 - t - u) (49 / 90)
  let z := (1 - t - 3 * u) * v
  invPoly3 t (8 / 33) * invPoly3 u (8 / 33) * v *
    (1 + 2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5)
/-- LEAF. Page 279: the polynomial is below the source logarithmic kernel on the whole closed domain. -/
theorem polynomial4_le (t u : ℝ) (htl : 41 / 180 ≤ t) (htu : t ≤ 8 / 33)
    (hul : 41 / 90 - t ≤ u) (huu : u ≤ t) :
    polynomial4 t u ≤
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by sorry

#print axioms region4_argument
#print axioms region4_kernel
#print axioms log_three_terms
#print axioms polynomial4_le
end
end LeanLab.Languasco2004.Kernel568
