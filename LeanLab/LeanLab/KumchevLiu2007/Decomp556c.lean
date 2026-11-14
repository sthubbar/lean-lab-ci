/-
Task556 exact downstream supplies for elementary admissions in SPLIT_bv_remainder.
Existing files remain sealed. The distribution consequence is CONDITIONAL ON the
maximal prime Bombieri Vinogradov input already isolated by Task542.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp542a

namespace LeanLab.KumchevLiu2007.Task556c

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task506b
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 17 sieve level logarithm, exact clean supply for the existing leaf. -/
theorem sieve_level_log_scale (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ d : ℕ, 1 ≤ d →
      d ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ → 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := by
  refine ⟨Real.exp 1, Real.exp_pos _, ?_⟩
  intro X hX d hd hdD
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hX
  have hL : 1 ≤ Real.log X := by
    calc 1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
         _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) hX
  have hD : Y X ε ^ (1 / 9 : ℝ) ≤ X := by
    rw [Y, ← Real.rpow_mul hXpos.le]
    calc X ^ ((7 / 12 + ε / 2) * (1 / 9 : ℝ)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by nlinarith)
         _ = X := Real.rpow_one X
  have hdR : (d : ℝ) ≤ X :=
    ((Nat.cast_le (α := ℝ)).mpr hdD).trans ((Nat.floor_le (Real.rpow_nonneg (by unfold Y; positivity) _)).trans hD)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlogd := Real.log_le_log hdpos hdR
  linarith

/-- Page 17 large parameter side conditions, exact clean supply for the existing leaf. -/
theorem sieve_regime (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X →
      1 ≤ Real.log X ∧ 1 ≤ Y X ε ^ (1 / 9 : ℝ) ∧ 0 ≤ errorScale X ε A := by
  refine ⟨Real.exp 1, Real.exp_pos _, ?_⟩
  intro X hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hX
  have hL : 1 ≤ Real.log X := by
    calc 1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
         _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) hX
  refine ⟨hL, ?_, ?_⟩
  · unfold Y
    rw [← Real.rpow_mul hXpos.le]
    exact Real.one_le_rpow hX1 (by positivity)
  · unfold errorScale Y
    positivity

/-- Page 17 weighted discrepancy, CONDITIONAL ON the existing maximal prime BV leaf. -/
theorem weighted_modulus_discrepancy (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ)) ≤ C * errorScale X ε (A + 1) := by
  obtain ⟨C, X0, hC, hb⟩ := Task542a.bv_remainder_from_maximal (A + 1) B ε (by linarith) hB hε hε1
  refine ⟨C, X0, hC, ?_⟩
  intro X hX n hn hXn hnle
  apply le_trans (Finset.sum_le_sum ?_) (hb X hX n hn hXn hnle)
  intro d hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  exact div_le_self (by positivity) (by linarith [Real.log_nonneg hd1])

end LeanLab.KumchevLiu2007.Task556c
