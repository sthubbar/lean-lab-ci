/-
AI wrote this Lean code for CODEX task276.
P0004 pages 22 to 26 equations 3.116 to 3.156.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.Decomp105
import LeanLab.HardyLittlewood1923.DecompJ203

namespace LeanLab.HardyLittlewood1923.Decomp276a

open Real Finset
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp105

/-- Reduced rational points of order N between minus one and two.
P0004 page 5 section 1.4 and page 22 equation 3.116, with translates for the arc about zero. -/
def fareyPoints (N : ℕ) : Finset ℚ :=
  (Icc 1 N).biUnion fun q =>
    ((Icc (-(q : ℤ)) (2 * (q : ℤ))).filter fun p => p.natAbs.Coprime q).image
      fun p : ℤ => (p : ℚ) / q

/-- The preceding Farey fraction, including the translate to the left of zero.
P0004 page 22 equation 3.116. The default is used only outside the intended range. -/
def fareyPrev (N : ℕ) (r : ℚ) : ℚ :=
  let s := (fareyPoints N).filter fun t => t < r
  if h : s.Nonempty then s.max' h else r - 1

/-- The following Farey fraction.
P0004 page 22 equation 3.116. The default is used only outside the intended range. -/
def fareyNext (N : ℕ) (r : ℚ) : ℚ :=
  let s := (fareyPoints N).filter fun t => r < t
  if h : s.Nonempty then s.min' h else r + 1

/-- The mediant of two reduced rational fractions.
P0004 page 5 section 1.4 and page 22 equation 3.116. -/
def mediant (r s : ℚ) : ℚ :=
  (r.num + s.num : ℤ) / ((r.den + s.den : ℕ) : ℚ)

/-- The left angular endpoint relative to p over q, in radians.
P0004 page 22 equation 3.118. -/
noncomputable def arcLeft (N p q : ℕ) : ℝ :=
  let r : ℚ := (p : ℚ) / q
  2 * π * ((mediant (fareyPrev N r) r : ℚ) - r : ℚ)

/-- The right angular endpoint relative to p over q, in radians.
P0004 page 22 equation 3.118. -/
noncomputable def arcRight (N p q : ℕ) : ℝ :=
  let r : ℚ := (p : ℚ) / q
  2 * π * ((mediant r (fareyNext N r) : ℚ) - r : ℚ)

/-- The model rational arc integral at r equal to three.
P0004 page 25 equation 3.151, parametrized by Y equal to 1/n minus i theta. -/
noncomputable def modelArc (n p q : ℕ) : ℂ :=
  (1 / (2 * π : ℂ)) * ((μ q : ℂ) / (q.totient : ℂ)) ^ 3 *
    ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
      ((1 / (n : ℂ)) - Complex.I * θ) ^ (-3 : ℤ) *
        Complex.exp ((n : ℂ) * ((1 / (n : ℂ)) - Complex.I * θ))

/-- The finite Farey model sum before extending its local integrals.
P0004 page 25 equation 3.142. -/
noncomputable def fareyModel (n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
    Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) * modelArc n p q

/-- P0004 page 5 section 1.4. A concrete Farey predecessor at order two. -/
theorem fareyPrev_two_zero : fareyPrev 2 0 = -1 / 2 := by decide +kernel

/-- P0004 page 5 section 1.4. A concrete Farey successor at order two. -/
theorem fareyNext_two_zero : fareyNext 2 0 = 1 / 2 := by decide +kernel

/-- P0004 page 5 section 1.4. The joined left endpoint for the zero arc at order two. -/
theorem arcLeft_two_zero_one : arcLeft 2 0 1 = -2 * π / 3 := by
  simp only [arcLeft, Nat.cast_zero, zero_div, sub_zero, fareyPrev_two_zero]
  rw [show mediant (-1 / 2) 0 = -1 / 3 by decide +kernel]
  norm_num; ring

/-- P0004 page 5 section 1.4. The joined right endpoint for the zero arc at order two. -/
theorem arcRight_two_zero_one : arcRight 2 0 1 = 2 * π / 3 := by
  simp only [arcRight, Nat.cast_zero, zero_div, sub_zero, fareyNext_two_zero]
  rw [show mediant 0 (1 / 2) = 1 / 3 by decide +kernel]
  norm_num; ring

/-- LEAF. P0004 pages 22 to 25 equations 3.116 to 3.142.
The generating function error is bounded before evaluating the model integrals.
This leaf contains no singular series main term. -/
theorem coefficient_to_farey {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 25 equations 3.151 to 3.155.
Extending the model integrals gives an unconditional error of order n to three halves.
This leaf contains no generating function coefficient and no zero free hypothesis. -/
theorem farey_to_finite :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖fareyModel n - (finiteMain n : ℂ)‖ ≤
        C * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n ^ B := by
  sorry

/-- P0004 page 26 equation 3.156, the triangle inequality assembly.
CONDITIONAL on the OPEN model evaluation leaf. -/
theorem finite_approximation_of_farey {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ)
    (hCoeff : ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  obtain ⟨B, C, n₀, hC⟩ := hCoeff
  obtain ⟨D, K, m₀, hK⟩ := farey_to_finite
  refine ⟨max B D, |C| + |K|, max (max n₀ m₀) 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hm0 : m₀ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hB : Real.log n ^ B ≤ Real.log n ^ max B D :=
    pow_le_pow_right₀ hlog (le_max_left _ _)
  have hD : Real.log n ^ D ≤ Real.log n ^ max B D :=
    pow_le_pow_right₀ hlog (le_max_right _ _)
  have hc := hC n hn0
  have hk := hK n hm0
  have hc' : C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B ≤
      |C| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ max B D := by
    calc _ ≤ |C| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
           gcongr; exact le_abs_self C
         _ ≤ _ := by gcongr
  have hk' : K * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n ^ D ≤
      |K| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ max B D := by
    calc _ ≤ |K| * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n ^ D := by
           gcongr; exact le_abs_self K
         _ ≤ _ := by gcongr
  have ht : ‖(nur 3 n : ℂ) - (finiteMain n : ℂ)‖ ≤
      ‖(nur 3 n : ℂ) - fareyModel n‖ + ‖fareyModel n - (finiteMain n : ℂ)‖ := by
    calc _ = ‖((nur 3 n : ℂ) - fareyModel n) +
          (fareyModel n - (finiteMain n : ℂ))‖ := by congr 1; ring
         _ ≤ _ := norm_add_le _ _
  have heq : ‖(nur 3 n : ℂ) - (finiteMain n : ℂ)‖ = |nur 3 n - finiteMain n| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [heq] at ht
  calc _ ≤ ‖(nur 3 n : ℂ) - fareyModel n‖ + ‖fareyModel n - (finiteMain n : ℂ)‖ := ht
       _ ≤ _ := by nlinarith only [hc, hk, hc', hk']

/-- P0004 page 26 equation 3.156. The exact sealed lower range target.
CONDITIONAL on the two OPEN leaves. -/
theorem finite_approximation_lower {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  exact finite_approximation_of_farey hΘ0 (coefficient_to_farey hΘ0 hΘ1 hZ)

#print axioms finite_approximation_of_farey
#print axioms fareyPrev_two_zero
#print axioms fareyNext_two_zero
#print axioms arcLeft_two_zero_one
#print axioms arcRight_two_zero_one
#print axioms coefficient_to_farey
#print axioms farey_to_finite
#print axioms finite_approximation_lower

end LeanLab.HardyLittlewood1923.Decomp276a
