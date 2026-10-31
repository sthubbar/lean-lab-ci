/-
P0095 Lu 2010, page 2365 equation 28, even singular series.
CODEX task47, unit U-8099. AI wrote this Lean code. Binary Goldbach is open.
The explicit even Euler product has a lower bound of 1.3.
Equality with Lu's Ramanujan series is not proved in this file.
-/
import LeanLab.ExceptionalSet.BG2026Prop81MPR
import LeanLab.ChenExplicit.TwinCNumeric

namespace LeanLab.ExceptionalSet.Lu2010Singular
open LeanLab.ExceptionalSet.BG2026

/-- The twin constant definitions in the two parts of the lab are identical. -/
theorem C0_eq_twinC : C0 = LeanLab.ChenExplicit.twinC := rfl

/-- The explicit product used for the even singular series is at least 1.3. -/
theorem singular_product_ge_thirteen_tenths (N : ℕ) : (13 / 10 : ℝ) ≤ Sing N := by
  have hC : (65 / 100 : ℝ) ≤ C0 := by
    rw [C0_eq_twinC]
    exact LeanLab.ChenExplicit.twinC_ge_065
  have hS := Sing_ge N
  linarith

/-- The elementary lower bound needed when choosing this product for InputsL.S. -/
theorem singular_product_ge_one (N : ℕ) : (1 : ℝ) ≤ Sing N := by
  have h := singular_product_ge_thirteen_tenths N
  linarith

/-- Nonzero even input for the lower bound. -/
theorem instance_four : Even 4 ∧ (1 : ℝ) ≤ Sing 4 :=
  ⟨by decide, singular_product_ge_one 4⟩

end LeanLab.ExceptionalSet.Lu2010Singular

#print axioms LeanLab.ExceptionalSet.Lu2010Singular.C0_eq_twinC
#print axioms LeanLab.ExceptionalSet.Lu2010Singular.singular_product_ge_thirteen_tenths
#print axioms LeanLab.ExceptionalSet.Lu2010Singular.singular_product_ge_one
#print axioms LeanLab.ExceptionalSet.Lu2010Singular.instance_four
