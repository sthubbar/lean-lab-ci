import LeanLab.RieselVaughan1983.Lemma2Local
import LeanLab.RieselVaughan1983.Stieltjes1Enclosure
import LeanLab.RieselVaughan1983.Lemma8

/-!
Lemma 2 on page 50, with the constants of pages 46 and 47.
AI wrote the Lean code. Binary Goldbach is OPEN.
Lemma2P is a statement, not a proof of Lemma 2.
-/

namespace LeanLab.RieselVaughan1983.Lemma2

open Finset Real

noncomputable section

/-- Equation 3.2. -/
def S (y : ℝ) : ℝ := ∑ q ∈ Icc 1 ⌊y⌋₊, sieveCoeff q

/-- Equation 2.7. -/
def H (w : ℝ) : ℝ := ∑' m : ℕ, |g m| * (m : ℝ) ^ (-w)

/-- Equation 2.9, with the sum over all primes. -/
def A0 : ℝ := ∑' p : ℕ, if p.Prime then Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) else 0

/-- Equation 2.10. -/
def A1 : ℝ := Real.log 2 / 2 + 2 * A0

/-- Equation 2.11, including the prime 2. -/
def A2 : ℝ := ∑' p : ℕ, if p.Prime then
  (8 * (p : ℝ) ^ 2 - 10 * p + 4) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) *
    Real.log p ^ 2 else 0

/-- Equation 2.12. -/
def A3 : ℝ := 4 * eulerMascheroniConstant + 2 * A1

/-- Equation 2.13. -/
def A4 : ℝ := A3 ^ 2 / 4 - 2 * eulerMascheroniConstant ^ 2 -
  4 * stieltjes1 + Real.log 2 ^ 2 / 4 - A2

/-- Equation 2.15. -/
def A5 : ℝ := 3282 / 1000 * Ctw * H (-(1 / 3 : ℝ))

/-- Lemma 2 on page 50, stated without asserting the missing moment evaluations. -/
def Lemma2P : Prop := ∀ y : ℝ, 1 ≤ y →
  |2 * Ctw * S y - Real.log y ^ 2 - A3 * Real.log y - A4| <
    A5 * y ^ (-(1 / 3 : ℝ))

lemma S_one : S 1 = 1 := by simp [S, sieveCoeff_one]

/-- The algebra from equation 3.8 and the page 51 moment displays to Lemma 2. -/
lemma main_term_identity (C a1 a2 gamma gamma1 t : ℝ) (hC : C ≠ 0) :
    2 * C *
      ((t ^ 2 / 2 + 2 * gamma * t + gamma ^ 2 - 2 * gamma1) / C +
        (t + 2 * gamma) * (a1 / C) +
        (Real.log 2 ^ 2 / 4 - a2 + a1 ^ 2) / C / 2) =
      t ^ 2 + (4 * gamma + 2 * a1) * t +
        ((4 * gamma + 2 * a1) ^ 2 / 4 - 2 * gamma ^ 2 - 4 * gamma1 +
          Real.log 2 ^ 2 / 4 - a2) := by
  field_simp [hC]
  ring

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.S_one
#print axioms LeanLab.RieselVaughan1983.Lemma2.main_term_identity
