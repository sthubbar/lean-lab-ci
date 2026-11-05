import LeanLab.HardyLittlewood1923.Decomp354a
import LeanLab.HardyLittlewood1923.Decomp354b

/-!
AI wrote this Lean code for CODEX task354.
P0004 page 26 equation 3.156.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354i

open Real Finset
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp105
open LeanLab.HardyLittlewood1923.Decomp276a

/-- P0004 page 26 equation 3.156.
The triangle inequality assembly now uses the proved model evaluation.
CONDITIONAL on the supplied coefficient bound. The model evaluation is proved. -/
theorem finite_approximation_of_farey {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ)
    (hCoeff : ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  obtain ⟨B, C, n₀, hC⟩ := hCoeff
  obtain ⟨D, K, m₀, hK⟩ := Decomp354a.farey_to_finite
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

/-- P0004 page 26 equation 3.156.
The full lower range target depends only on the new supply leaves.
CONDITIONAL on primeSeries_square_mean, coefficient_transfer,
and lemma9_on_circle. -/
theorem finite_approximation_lower {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  exact finite_approximation_of_farey hΘ0 (Decomp354b.coefficient_to_farey hΘ0 hΘ1 hZ)


#print axioms finite_approximation_of_farey
#print axioms finite_approximation_lower

end LeanLab.HardyLittlewood1923.Decomp354i
