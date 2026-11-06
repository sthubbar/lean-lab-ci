/-
P0093 page 158 equation 4.8. Elementary bridges for the fresh main Mellin split.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_mellin_near357

namespace LeanLab.Linnik1951

/-- P0093 page 158 equation 4.8, interval length reduction.
Exact near_half_integral_le_sup357 type from the fresh main split.
Continuity and the existing Mathlib integral monotonicity theorem suffice. -/
theorem near_half_integral_proved412 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (M u v : ℝ) (hN : 1 ≤ N) (huv : u ≤ v)
    (hM : ∀ α : ℝ, α ∈ Set.Icc u v → ‖characterPrime280 χ N α‖ ^ 2 ≤ M) :
    (∫ α in u..v, ‖characterPrime280 χ N α‖ ^ 2) ≤ M * (v - u) := by
  have hi : IntervalIntegrable (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2)
      MeasureTheory.volume u v :=
    ((continuous_character_prime357 χ N hN).norm.pow 2).intervalIntegrable u v
  calc
    _ ≤ ∫ _α in u..v, M :=
      intervalIntegral.integral_mono_on huv hi intervalIntegrable_const hM
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- P0093 page 158 equation 4.8, enlargement to the required scale.
Exact near_constant_selection357 type from the fresh main split.
Once log N is at least one and tau is at most N, multiplication by
N over tau times log N only enlarges the nonnegative expression. -/
theorem near_constant_selection_proved412 (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (8 : ℝ) * C * Real.log N ^ 5 / (q : ℝ) ≤
          (8 * C) * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨max 1 N0, ?_⟩
  intro N hN q hq hqt
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNN : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast h1.le
  have hlog : 1 ≤ Real.log N := by
    have hN0R : (N0 : ℝ) < N := by exact_mod_cast hNN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hN0.trans hN0R).le
  have hτp : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hτ : (N : ℝ) ^ (1 / 7 : ℝ) ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
      _ = _ := Real.rpow_one _
  have hratio : 1 ≤ (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) :=
    (le_div_iff₀ hτp).mpr (by simpa using hτ)
  have hb : 1 ≤ (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N :=
    one_le_mul_of_one_le_of_one_le hratio hlog
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  calc
    _ ≤ ((8 : ℝ) * C * Real.log N ^ 5 / (q : ℝ)) *
        ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N) :=
      le_mul_of_one_le_right (by positivity) hb
    _ = _ := by field_simp <;> ring

/-- P0093 page 158 final sentence. Exact near_negative_sup357 type
from the fresh main split. The already proved character reflection
removes an independent negative side obligation. CONDITIONAL only on
the corresponding fresh positive supremum input. -/
theorem near_negative_sup_decomposed412 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ, -(4 / (N : ℝ)) ≤ α →
          α ≤ 0 →
          ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  obtain ⟨C, hC, N0, hp⟩ := near_positive_sup357 hG
  refine ⟨C, hC, N0, ?_⟩
  intro N hN q hq hqt χ hχ α hαlo hαhi
  have hstar : star χ ≠ 1 := by
    intro h
    apply hχ
    simpa only [star_star, star_one] using congrArg star h
  have hb := hp N hN q hq hqt (star χ) hstar (-α) (by linarith) (by linarith)
  have he := character_norm_reflect357 χ N (-α)
  simp only [neg_neg] at he
  rw [he]
  exact hb

end LeanLab.Linnik1951
