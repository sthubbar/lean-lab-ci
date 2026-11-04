/-
AI wrote this Lean code for CODEX task276.
P0004 page 23 equations 3.121 to 3.124.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.Decomp276b

namespace LeanLab.HardyLittlewood1923.Decomp276c

open Real Finset
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp105
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b

/-- The angle between Y and the imaginary axis.
P0004 page 23 after equation 3.121, including its continuous value at theta zero. -/
noncomputable def angularGap (n : ℕ) (θ : ℝ) : ℝ :=
  π / 2 - |Complex.arg (localY n θ)|

/-- The angular error factor in the rational arc bound.
P0004 page 23 equation 3.121. -/
noncomputable def angularTerm (Θ : ℝ) (n q : ℕ) (θ : ℝ) : ℝ :=
  Real.sqrt q * ‖localY n θ‖ ^ (-Θ) * (angularGap n θ) ^ (-Θ - 1 / 2) *
    Real.log (1 / angularGap n θ + 2)

/-- P0004 page 23 after equation 3.121. The gap is positive when n is positive. -/
theorem angularGap_pos {n : ℕ} (hn : 0 < n) (θ : ℝ) : 0 < angularGap n θ := by
  exact sub_pos.mpr (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl
    (by rw [localY_re]; positivity)))

/-- P0004 page 23 equation 3.122. The small angle case includes theta zero. -/
theorem angularGap_zero (n : ℕ) : angularGap n 0 = π / 2 := by
  simp [angularGap, localY_zero]

/-- P0004 page 23 equation 3.123. A concrete point in the large angle case at n equal to four. -/
theorem half_mem_zero_arc :
    (1 / 2 : ℝ) ∈ Set.Icc (arcLeft (Nat.sqrt 4) 0 1) (arcRight (Nat.sqrt 4) 0 1) := by
  rw [show Nat.sqrt 4 = 2 by decide +kernel, arcLeft_two_zero_one, arcRight_two_zero_one]
  constructor <;> linarith [Real.pi_gt_three]

/-- LEAF. P0004 page 23 equation 3.121, from Lemma 9 equation 2.823.
This preliminary estimate retains the angular factor instead of the final uniform bound. -/
theorem preliminary_arc_error {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤
          C * ((n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ) * Real.log n ^ A := by
  sorry

/-- LEAF. P0004 page 23 equation 3.122 and the sentence after equation 3.123.
The small angle estimate is elementary and uses no zero free premise. -/
theorem angular_small {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 4 ≤ n → ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n →
      ∀ θ : ℝ, |θ| ≤ 1 / (n : ℝ) →
        angularTerm Θ n q θ ≤ D * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
  sorry

/-- LEAF. P0004 page 23 equation 3.123.
The large angle estimate uses the Farey width and no zero free premise. -/
theorem angular_large {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
      1 / (n : ℝ) < |θ| →
        angularTerm Θ n q θ ≤ E * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
  sorry

/-- P0004 page 23 equation 3.124, by its two angular cases.
CONDITIONAL on the three OPEN leaves in this file. -/
theorem uniform_arc_error {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ C * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A := by
  obtain ⟨A, C, hC, n₀, hc⟩ := preliminary_arc_error hΘ0 hΘ1 hZ
  obtain ⟨D, hD, hd⟩ := angular_small hΘ0 hΘ1
  obtain ⟨E, hE, he⟩ := angular_large hΘ0 hΘ1
  refine ⟨A + 1, C * (1 + D + E), max n₀ 4, fun n hn q hq hqN p hp hpq θ hθ => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hl : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
  have hx : 0 ≤ (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by positivity
  have ha : angularTerm Θ n q θ ≤ (D + E) * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
    by_cases hs : |θ| ≤ 1 / (n : ℝ)
    · have h := hd n hn4 q hq hqN θ hs
      nlinarith only [h, mul_nonneg hE hx]
    · have h := he n hn4 q hq hqN p hp hpq θ hθ (lt_of_not_ge hs)
      nlinarith only [h, mul_nonneg hD hx]
  have hpw : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
    calc _ ≤ (n : ℝ) ^ (Θ + 1 / 4) :=
           Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
         _ ≤ _ := le_mul_of_one_le_right (by positivity) hl
  have hsum : (n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ ≤
      (1 + D + E) * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
    nlinarith only [hpw, ha]
  calc _ ≤ C * ((n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ) * Real.log n ^ A :=
           hc n hn0 q hq hqN p hp hpq θ hθ
       _ ≤ C * ((1 + D + E) * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n) * Real.log n ^ A :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hC) (by positivity)
       _ = _ := by rw [pow_succ]; ring

/-- P0004 page 23 equation 3.124 feeds the later integrations.
This is the exact sealed uniform_rational_arc statement from DecompJ203.
CONDITIONAL on the OPEN leaves here, the square mean transfer and the model evaluation. -/
theorem uniform_rational_arc {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  exact finite_approximation_of_farey hΘ0
    (coefficient_error_of_uniform hΘ0 hΘ1 (uniform_arc_error hΘ0 hΘ1 hZ))

#print axioms half_mem_zero_arc
#print axioms angularGap_pos
#print axioms angularGap_zero
#print axioms preliminary_arc_error
#print axioms angular_small
#print axioms angular_large
#print axioms uniform_arc_error
#print axioms uniform_rational_arc

end LeanLab.HardyLittlewood1923.Decomp276c
