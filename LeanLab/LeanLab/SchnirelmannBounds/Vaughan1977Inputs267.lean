/-
Vaughan 1977 pages 95 to 106.
https://doi.org/10.1515/crll.1977.290.93
Connect the proved numerical inputs to the existing paper assemblies.
The representation sieve still uses the open weighted large sieve leaf.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Decomp1525b
import LeanLab.SchnirelmannBounds.Vaughan1977Constant
import LeanLab.Ported.Prove2Me.Decomp1525cLink

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977Inputs267
open Decomp1525a Decomp1525b

/-- The constant conventions in the two existing routes agree. -/
theorem Cv_eq_twinC : Cv = LeanLab.ChenExplicit.twinC := by rfl

/-- Equation 2.10 supplies both numerical hypotheses of Lemmas 7 and 8. -/
theorem Cv_bounds : 0.6601 < Cv ∧ Cv < 0.6602 := by
  rw [Cv_eq_twinC]
  exact ⟨Vaughan1977Constant.twinC_gt_06601, Vaughan1977Twin.C_lt⟩

/-- The full Lemma 7 with its numerical constant input discharged. -/
theorem lemma7 (x : ℝ) (hx : 10 ^ 9 ≤ x) (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    0 < Sn n (zz x) (zz x)⁻¹ ∧
    (Sn n (zz x) (zz x)⁻¹)⁻¹ <
      16 * Cv / ((alpha x + Real.log x) * Real.log x) * singQ n - 2 / Real.sqrt x := by
  exact lemma7_of Cv_bounds x hx n hn hn0

/-- The singular factor agrees with the rational product for every nonzero argument. -/
theorem singQ_eq_prodQ (n : ℕ) (hn : n ≠ 0) :
    singQ n = (Vaughan1977Lemma10.prodQ n : ℝ) := by
  simp only [Vaughan1977Lemma10.prodQ, Rat.cast_prod, Rat.cast_div, Rat.cast_sub,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
  rw [Vaughan1977Eq56.oddPF_eq hn]
  rfl

/-- Lemma 8 in the original route, conditional on the open weighted large sieve leaf. -/
theorem lemma8 : Vaughan1977Lemma10.Lemma8 LeanLab.ChenExplicit.twinC := by
  intro x hx h he hh
  have hh0 : h ≠ 0 := by
    intro hh0
    subst h
    rcases hh with hh | hh
    · omega
    · norm_num at hh
      linarith
  have h := lemma8_of Cv_bounds x hx h he hh
  rw [singQ_eq_prodQ _ (Nat.ne_of_gt (Int.natAbs_pos.mpr hh0)), Cv_eq_twinC] at h
  exact h

/-- The proved Euler product supplies the finite mass input. -/
theorem massBound : Vaughan1977Moments.MassBound 6.2130 := by
  exact Vaughan1977Euler.mass_of_euler eulerMass_62130

/-- The proved Euler product supplies the finite moment input. -/
theorem momentBound : Vaughan1977Moments.MomentBound := by
  exact Vaughan1977Euler.moment_of_euler eulerMoment_1446

/-- The explicit tail estimate with only Brun Titchmarsh and equation 2.15 as inputs. -/
theorem eq510tail (hBT : Vaughan1977Lemma3.Lemma3Coprime)
    (h215 : Vaughan1977Lemma11Inputs.Eq215) : Vaughan1977Eq55.Eq510tail 6.2130 := by
  exact Vaughan1977Moments.eq510tail_of_moments (by norm_num) hBT
    (Vaughan1977Lemma11Inputs.thetaUpper_of_eq215 h215) massBound momentBound

/-- The original 27 prime route with its remaining analytic inputs explicit. -/
theorem statement27_of_analytic_inputs (hRS : LeanLab.RieselVaughan1983.RS33)
    (h8 : Vaughan1977Lemma10.Lemma8 LeanLab.ChenExplicit.twinC)
    (hBT : Vaughan1977Lemma3.Lemma3Coprime) (h215 : Vaughan1977Lemma11Inputs.Eq215) :
    Vaughan1977.Statement27 := by
  exact Vaughan1977Moments.statement27_of_moments (C := 6.2130) (by norm_num) (by norm_num) hRS h8
    (LeanLab.Ported.Prove2Me.Decomp1525cLink.lemma11_of_eq215 h215) hBT
    (Vaughan1977Lemma11Inputs.thetaUpper_of_eq215 h215) massBound momentBound

/-- The same route using Lemma 8, conditional on the open weighted large sieve leaf. -/
theorem statement27 (hRS : LeanLab.RieselVaughan1983.RS33)
    (hBT : Vaughan1977Lemma3.Lemma3Coprime) (h215 : Vaughan1977Lemma11Inputs.Eq215) :
    Vaughan1977.Statement27 := by
  exact statement27_of_analytic_inputs hRS lemma8 hBT h215

example : (10 : ℝ)^9 ≤ 10^9 ∧ Even (2 : ℕ) ∧ 0 < (2 : ℕ) := by norm_num
example : singQ 6 = 2 := by norm_num [singQ, Nat.primeFactors, Finset.filter_insert, Finset.filter_singleton]
example : (∑ d ∈ Icc 1 (1 : ℕ), Vaughan1977Moments.a d) = 1 := by
  simp [Vaughan1977Moments.a_one]

end LeanLab.SchnirelmannBounds.Vaughan1977Inputs267

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.Cv_eq_twinC

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.Cv_bounds

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.lemma7

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.singQ_eq_prodQ

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.lemma8

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.massBound

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.momentBound

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.eq510tail

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.statement27_of_analytic_inputs

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Inputs267.statement27
