import Mathlib

/-!
An elementary order lemma for the Laplace representation in Lemma 2.3.
Source: Zhao 2025, displays 2.22 and 2.24, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- A nonnegative continuous kernel has an antitone Laplace integral on a nonnegative interval. -/
theorem weighted_integral_antitone (f : ℝ → ℝ) (a b l L : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hl : l ≤ L) (hf : Continuous f)
    (hf0 : ∀ u ∈ Set.Icc a b, 0 ≤ f u) :
    (∫ u in a..b, f u * Real.exp (-L * u)) ≤
      ∫ u in a..b, f u * Real.exp (-l * u) := by
  have hcont (r : ℝ) : Continuous (fun u => f u * Real.exp (-r * u)) := by fun_prop
  apply intervalIntegral.integral_mono_on hab
    ((hcont L).intervalIntegrable a b) ((hcont l).intervalIntegrable a b)
  intro u hu
  apply mul_le_mul_of_nonneg_left _ (hf0 u hu)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (ha.trans hu.1)]

#print axioms weighted_integral_antitone

end LeanLab.Zhao2025.Task56
