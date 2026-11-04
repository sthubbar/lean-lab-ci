import LeanLab.HardyLittlewood1923.Decomp105

/-!
AI wrote this Lean code for CODEX task296.
P0004 page 21 equation 3.113 and page 26 equation 3.156.
This proves the finite approximation on even arguments without Hypothesis R.
Binary Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp296Parity

open Real
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp105

/-- P0004 page 26 equation 3.156, the unlike parity specialization at r equal to three. -/
theorem finite_approximation_even {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) :
    ∃ C : ℝ, ∀ n : ℕ, 4 ≤ n → Even n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ 3 := by
  obtain ⟨D, hD⟩ := tail_at_target hΘ
  refine ⟨18 + |D|, fun n hn he => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
  have hlog3 : 1 ≤ Real.log n ^ 3 := one_le_pow₀ hlog
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) := by
    calc _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hc := nur_unlike_le 1 n (by rw [Nat.even_iff.mp he]; norm_num)
  have hc' : nur 3 n ≤ 18 * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ 3 := by
    calc _ ≤ 9 * ((n : ℝ) + 1) * Real.log n ^ 3 := by norm_num at hc ⊢; exact hc
      _ ≤ 18 * (n : ℝ) * Real.log n ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := by gcongr
  have ht := hD n hn
  rw [sing3_even he, mul_zero, sub_zero] at ht
  have ht' : |finiteMain n| ≤ |D| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ 3 := by
    calc _ ≤ D * (n : ℝ) ^ (2 + (Θ - 3 / 4)) := ht
      _ ≤ |D| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) := by gcongr; exact le_abs_self D
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hlog3
  calc _ ≤ |nur 3 n| + |finiteMain n| := abs_sub _ _
    _ = nur 3 n + |finiteMain n| := by rw [abs_of_nonneg (nur_nonneg _ _)]
    _ ≤ _ := by nlinarith only [hc', ht']

#print axioms finite_approximation_even

end LeanLab.HardyLittlewood1923.Decomp296Parity
