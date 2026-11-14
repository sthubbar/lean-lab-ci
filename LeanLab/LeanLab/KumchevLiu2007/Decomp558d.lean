/-
Elementary supplies for the older modulus remainder split.
Source: Kumchev and Liu page 17 between displays 57 and 58.
The sealed split file is unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp542a

namespace LeanLab.KumchevLiu2007.Task558d
open Real Task506b
open scoped BigOperators Topology

/-- Page 17 level D equal to Y to one ninth, the exact elementary logarithmic
level statement of the older split. -/
theorem sieve_level_log_scale_supply (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ d : ℕ, 1 ≤ d →
      d ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ → 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := by
  refine ⟨Real.exp 1, Real.exp_pos _, ?_⟩
  intro X hX d hd1 hdD
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hL : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hY : 0 < Y X ε := Real.rpow_pos_of_pos hXp _
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdle : (d : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) :=
    (Nat.le_floor_iff (Real.rpow_nonneg hY.le _)).mp hdD
  have hl := Real.log_le_log (by linarith : (0 : ℝ) < d) hdle
  rw [Real.log_rpow hY, Y, Real.log_rpow hXp] at hl
  have hθ : 7 / 12 + ε / 2 ≤ (8 / 9 : ℝ) := by linarith
  have hθL := mul_le_mul_of_nonneg_right hθ (by linarith : 0 ≤ Real.log X)
  nlinarith

/-- Page 17 after display 57, the exact elementary large X side conditions
of the older split. -/
theorem sieve_regime_supply (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X →
      1 ≤ Real.log X ∧ 1 ≤ Y X ε ^ (1 / 9 : ℝ) ∧ 0 ≤ errorScale X ε A := by
  refine ⟨Real.exp 1, Real.exp_pos _, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hX
  have hL : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hθ : 0 ≤ 7 / 12 + ε / 2 := by linarith
  have hY : 1 ≤ Y X ε := Real.one_le_rpow hX1 hθ
  refine ⟨hL, Real.one_le_rpow hY (by norm_num), ?_⟩
  unfold errorScale
  positivity

/-- Page 17 between displays 57 and 58, inserting a reciprocal logarithmic
weight decreases the nonnegative remainder. -/
theorem weighted_modulus_sum_le (X B ε : ℝ) (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
      (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        |progressionCount X B ε n d - density n d * primeMass X B ε| /
          (1 + Real.log (d : ℝ))) ≤ remainder X B ε n := by
  unfold remainder
  apply Finset.sum_le_sum
  intro d hd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  exact div_le_self (mul_nonneg (sq_nonneg _) (abs_nonneg _))
    (by linarith [Real.log_nonneg hdR])

/-- Page 17 between displays 57 and 58, the exact older weighted discrepancy
statement follows from the maximal prime BV transfer. CONDITIONAL ON
Task542a.maximal_bombieri_vinogradov. -/
theorem weighted_modulus_discrepancy_supply (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ)) ≤ C * errorScale X ε (A + 1) := by
  obtain ⟨C, X0, hC, h⟩ := Task542a.bv_remainder_from_maximal (A + 1) B ε (by linarith) hB hε hε1
  exact ⟨C, X0, hC, fun X hX n hn hXn hnle =>
    (weighted_modulus_sum_le X B ε n).trans (h X hX n hn hXn hnle)⟩

end LeanLab.KumchevLiu2007.Task558d
