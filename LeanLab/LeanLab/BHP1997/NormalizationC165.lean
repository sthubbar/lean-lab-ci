/-
P0069, page 52, displays 5.18, 5.22 and 5.23 imply condition 1.9.
The three squared error estimates combine with an absolute factor 9.
This is CONDITIONAL on the three actual mean square inputs.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.Thm2Statement

namespace LeanLab.BHP1997.NormalizationC165
open Classical Complex MeasureTheory

/-- Page 52, the pointwise three-error decomposition for replacing the
Perron center W by the constant-density center. The factor 3 follows
from the triangle inequality and the three-term Cauchy inequality. -/
theorem pointwise_three_errors (F W H U d : ℂ) :
    ‖F - d * U‖ ^ 2 ≤ 3 * (‖F - d * W‖ ^ 2 +
      ‖d * (W - H)‖ ^ 2 + ‖d * (H - U)‖ ^ 2) := by
  let a := F - d * W
  let b := d * (W - H)
  let c := d * (H - U)
  have heq : F - d * U = a + b + c := by dsimp [a, b, c]; ring
  have htri : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le a b) (le_refl ‖c‖))
  have hs := pow_le_pow_left₀ (norm_nonneg _) htri 2
  rw [heq]
  dsimp only [a, b, c] at hs ⊢
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]

/-- Page 52, integrating the three-error inequality and summing over
a finite character set. The three input bounds are explicit hypotheses.
This is the elementary assembly behind 5.18, 5.22 and 5.23. -/
theorem integrated_three_errors {α : Type*} (E : Finset α)
    (F : α → ℝ → ℂ) (d : α → ℂ) (W H U : ℝ → ℂ)
    {a b R1 R2 R3 : ℝ} (hab : a ≤ b)
    (h0 : ∀ χ ∈ E, IntervalIntegrable (fun y => ‖F χ y - d χ * U y‖ ^ 2) volume a b)
    (h1 : ∀ χ ∈ E, IntervalIntegrable (fun y => ‖F χ y - d χ * W y‖ ^ 2) volume a b)
    (h2 : ∀ χ ∈ E, IntervalIntegrable (fun y => ‖d χ * (W y - H y)‖ ^ 2) volume a b)
    (h3 : ∀ χ ∈ E, IntervalIntegrable (fun y => ‖d χ * (H y - U y)‖ ^ 2) volume a b)
    (hR1 : (∑ χ ∈ E, ∫ y in a..b, ‖F χ y - d χ * W y‖ ^ 2) ≤ R1)
    (hR2 : (∑ χ ∈ E, ∫ y in a..b, ‖d χ * (W y - H y)‖ ^ 2) ≤ R2)
    (hR3 : (∑ χ ∈ E, ∫ y in a..b, ‖d χ * (H y - U y)‖ ^ 2) ≤ R3) :
    (∑ χ ∈ E, ∫ y in a..b, ‖F χ y - d χ * U y‖ ^ 2) ≤ 3 * (R1 + R2 + R3) := by
  have hp (χ : α) (hχ : χ ∈ E) :
      (∫ y in a..b, ‖F χ y - d χ * U y‖ ^ 2) ≤
        3 * ((∫ y in a..b, ‖F χ y - d χ * W y‖ ^ 2) +
          (∫ y in a..b, ‖d χ * (W y - H y)‖ ^ 2) +
          ∫ y in a..b, ‖d χ * (H y - U y)‖ ^ 2) := by
    have hi := ((h1 χ hχ).add (h2 χ hχ)).add (h3 χ hχ)
    have hh := intervalIntegral.integral_mono hab (h0 χ hχ) (hi.const_mul 3)
      (fun y => pointwise_three_errors (F χ y) (W y) (H y) (U y) (d χ))
    simpa only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (h1 χ hχ) (h2 χ hχ),
      intervalIntegral.integral_add ((h1 χ hχ).add (h2 χ hχ)) (h3 χ hχ)] using hh
  have hsum := Finset.sum_le_sum hp
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  nlinarith

end LeanLab.BHP1997.NormalizationC165
