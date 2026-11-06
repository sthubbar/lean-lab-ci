import LeanLab.Halupczok2012.Circle398
import LeanLab.Halupczok2012.U1495PPS

/-!
Nonvacuity checks for the supply leaves and the existing Theorem2 hypotheses.
Source: Halupczok journal pages 333 to 334 and Perelli Pintz pages 43 to 44.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Instances398

open Finset
open scoped Classical ArithmeticFunction.vonMangoldt

/-- The common Theorem2 hypotheses hold on an unbounded family once Q = 1 is admissible. -/
theorem thm2_hyp_family (t : ℕ) (ht : 1 ≤ t) (ε ε1 ε2 B : ℝ)
    (he : ε ≤ 2 / 3) (he1 : ε1 ≤ 2 / 5) (he2 : ε2 ≤ 5 / 12)
    (hlevel : 1 ≤ (t : ℝ) * (t : ℝ) ^ (-(1 / 2) : ℝ) * Real.log t ^ (-B)) :
    Thm2Hyp ε ε1 ε2 B (fun i : Fin 7 => if i = 5 then 3 else 1)
      (6 * t + 1) t t t t 1 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hp (s : ℝ) (hs : s ≤ 1) : (t : ℝ) ^ s ≤ t := by
    simpa using Real.rpow_le_rpow_of_exponent_le htR hs
  have h1 := hp (3 / 5 + ε1) (by linarith)
  have h2 := hp (7 / 12 + ε2) (by linarith)
  have h3 := hp (1 / 3 + ε) (by linarith)
  unfold Thm2Hyp
  refine ⟨⟨3 * t, by omega⟩, le_rfl, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_⟩
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simp
  · push_cast
    linarith
  · norm_num
    linarith
  · norm_num
    linarith
  · simpa using hlevel

/-- The additional Q bound of Theorem2 is nonempty in the same family. -/
theorem secondary_level (t : ℝ) (ht : 6 ≤ t) :
    1 ≤ t ^ (3 / 2 : ℝ) * (5 * t + 1) ^ (-(1 / 2) : ℝ) := by
  have ht1 : 1 ≤ t := by linarith
  have hD : 0 < 5 * t + 1 := by linarith
  have hS : 0 < Real.sqrt (5 * t + 1) := Real.sqrt_pos.mpr hD
  have hs : Real.sqrt (5 * t + 1) ≤ t := by
    have he := Real.sq_sqrt hD.le
    have hz := Real.sqrt_nonneg (5 * t + 1)
    nlinarith
  have hp : t ≤ t ^ (3 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
  rw [Real.rpow_neg hD.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, le_div_iff₀ hS]
  simpa using hs.trans hp

/-- For every B there are arbitrarily large concrete natural parameters for all Theorem2 hypotheses. -/
theorem thm2_nonvacuous (B : ℝ) :
    ∃ t0 : ℕ, ∀ t : ℕ, t0 ≤ t →
      Thm2Hyp (1 / 12) (1 / 12) (1 / 12) B (fun i : Fin 7 => if i = 5 then 3 else 1)
        (6 * t + 1) t t t t 1 ∧
      1 ≤ (t : ℝ) ^ (3 / 2 : ℝ) * (((6 * t + 1 : ℕ) : ℝ) - t) ^ (-(1 / 2) : ℝ) ∧
      (1 : ℝ) ≤ ((6 * t + 1 : ℕ) : ℝ) - t - t ∧
      ∀ i : Fin 7, 0 < (if i = 5 then (3 : ℝ) else 1) := by
  obtain ⟨x0, hx0⟩ := pps_Q_one_eventually B
  refine ⟨max 6 ⌈x0⌉₊, ?_⟩
  intro t ht
  have ht6 : 6 ≤ t := (le_max_left _ _).trans ht
  have htR : (6 : ℝ) ≤ t := by exact_mod_cast ht6
  have hx : x0 ≤ (t : ℝ) := (Nat.le_ceil x0).trans (by exact_mod_cast (le_max_right _ _).trans ht)
  refine ⟨thm2_hyp_family t (by omega) _ _ _ B (by norm_num) (by norm_num) (by norm_num) (hx0 t hx), ?_, ?_, ?_⟩
  · convert secondary_level t htR using 1 <;> push_cast <;> ring
  · push_cast
    linarith
  · intro i
    split_ifs <;> norm_num

/-- The additive character and the two polynomials have a nonzero concrete value. -/
theorem polynomial_instance : Decomp398a.phase 0 = 1 ∧
    Decomp398a.firstPoly 5 5 0 = Decomp398a.secondPoly 5 0 := by
  constructor
  · exact LeanLab.PNTPort.LargeSieve.e_zero
  · simp only [Decomp398a.firstPoly, Decomp398a.secondPoly, sub_self]

end LeanLab.Halupczok2012.Instances398
