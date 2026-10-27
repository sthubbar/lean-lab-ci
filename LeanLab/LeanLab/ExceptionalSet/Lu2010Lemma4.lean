/-
CODEX task85 status: Lu2010FirstDerivative.secondDerivativeEstimate_proved proves the existing full SecondDerivativeEstimate with allowed axioms. This file is imported by that companion, so the proof is kept there to avoid a circular import.
AI wrote the Lean code. Binary Goldbach is open.
-/
/-
P0095 Lu 2010, page 2366 Lemma 4, cited there from reference 10.
CODEX task47, unit U-8098. AI wrote this Lean code. Binary Goldbach is open.
The full second derivative estimate is a cited Prop.
The short-interval case below follows just from the norm of the integrand.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.Lu2010Lemma4
open Real

/-- The oscillatory integral with the phase convention printed in Lemma 4. -/
noncomputable def osc (f : ℝ → ℝ) (a b : ℝ) : ℂ :=
  ∫ x in a..b, Complex.exp ((f x : ℂ) * Complex.I)

/-- Lu's cited Lemma 4, with global C2 regularity as a conservative smoothness restriction. -/
def SecondDerivativeEstimate : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → ∀ a b y : ℝ, a ≤ b → 0 < y →
    ((∀ x ∈ Set.Icc a b, y ≤ deriv (deriv f) x) ∨
      (∀ x ∈ Set.Icc a b, deriv (deriv f) x ≤ -y)) →
    ‖osc f a b‖ ≤ 8 * y ^ (-(1 / 2) : ℝ)

/-- Trivial interval length bound, valid without a derivative assumption. -/
theorem norm_osc_le (f : ℝ → ℝ) (a b : ℝ) : ‖osc f a b‖ ≤ |b - a| := by
  unfold osc
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (1 : ℝ)) (a := a) (b := b)
    (f := fun x => Complex.exp ((f x : ℂ) * Complex.I))
    (fun x _ => (Complex.norm_exp_ofReal_mul_I (f x)).le)

/-- The printed bound holds trivially when the interval is at most 8 over the square root of y. -/
theorem lemma4_short (f : ℝ → ℝ) {a b y : ℝ} (hab : a ≤ b) (hy : 0 < y)
    (hshort : y * (b - a) ^ 2 ≤ 64) :
    ‖osc f a b‖ ≤ 8 * y ^ (-(1 / 2) : ℝ) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hs2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hlen : b - a ≤ 8 / Real.sqrt y := by
    apply (le_div_iff₀ hs).mpr
    have hprod : 0 ≤ (b - a) * Real.sqrt y := by positivity
    nlinarith [sq_nonneg ((b - a) * Real.sqrt y - 8)]
  calc ‖osc f a b‖ ≤ |b - a| := norm_osc_le f a b
    _ = b - a := abs_of_nonneg (sub_nonneg.mpr hab)
    _ ≤ 8 / Real.sqrt y := hlen
    _ = 8 * y ^ (-(1 / 2) : ℝ) := by
      rw [Real.rpow_neg hy.le, Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- A nonzero interval and genuine positive curvature instance of the short case. -/
theorem quadratic_instance :
    (∀ x : ℝ, deriv (deriv (fun t : ℝ => t ^ 2)) x = 2) ∧
      ‖osc (fun t => t ^ 2) 0 1‖ ≤ 8 * (2 : ℝ) ^ (-(1 / 2) : ℝ) := by
  constructor
  · have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
      funext t
      simp
    intro x
    rw [hd]
    simp
  · exact lemma4_short _ (by norm_num) (by norm_num) (by norm_num)

end LeanLab.ExceptionalSet.Lu2010Lemma4

#print axioms LeanLab.ExceptionalSet.Lu2010Lemma4.norm_osc_le
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma4.lemma4_short
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma4.quadratic_instance
