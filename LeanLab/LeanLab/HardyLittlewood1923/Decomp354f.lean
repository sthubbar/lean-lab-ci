import LeanLab.HardyLittlewood1923.Decomp354c
import LeanLab.HardyLittlewood1923.Decomp354e

/-!
AI wrote this Lean code for CODEX task354.
P0004 page 23 equation 3.124.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354f

open Real
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp276c

/-- P0004 page 23 equation 3.124.
Use the new supply leaves and the independently proved small angle estimate.
CONDITIONAL on lemma9_on_circle. Both angular cases are proved. -/
theorem uniform_arc_error {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ C * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A := by
  obtain ⟨A, C, hC, n₀, hc⟩ := Decomp354c.preliminary_arc_error hΘ0 hΘ1 hZ
  obtain ⟨D, hD, hd⟩ := Decomp354d.angular_small hΘ0 hΘ1
  obtain ⟨E, hE, he⟩ := Decomp354e.angular_large hΘ0 hΘ1
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


#print axioms uniform_arc_error

end LeanLab.HardyLittlewood1923.Decomp354f
