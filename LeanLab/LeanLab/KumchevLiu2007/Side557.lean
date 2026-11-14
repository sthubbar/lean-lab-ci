/-
Elementary exact supplies for the old page 17 modulus scale leaves.
Source https://arxiv.org/abs/0801.0130 page 17 display 58.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp506bBase

namespace LeanLab.KumchevLiu2007.Task557d

open Task506b

/-- Page 17 display 58, the modulus logarithm is below twice log X.
This supplies the exact old elementary leaf without importing its target file. -/
theorem sieve_level_log_scale (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ d : ℕ, 1 ≤ d →
      d ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ → 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := by
  refine ⟨Real.exp 1, Real.exp_pos _, ?_⟩
  intro X hX d hd hdD
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hL : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hX
  have hY : 0 < Y X ε := Real.rpow_pos_of_pos hXp _
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdlevel : (d : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) := by
    exact (by exact_mod_cast hdD : (d : ℝ) ≤ (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ)).trans
      (Nat.floor_le (Real.rpow_nonneg hY.le _))
  have hh := Real.log_le_log hdR hdlevel
  rw [Real.log_rpow hY, Y, Real.log_rpow hXp] at hh
  have hcoef : (7 / 12 : ℝ) + ε / 2 ≤ 8 / 9 := by linarith
  have hm := mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤ Real.log X)
  nlinarith

#print axioms sieve_level_log_scale

/-- Page 17 display 58, the elementary large X regime has a fixed positive
threshold. This supplies the exact old side condition leaf. -/
theorem sieve_regime (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X →
      1 ≤ Real.log X ∧ 1 ≤ Y X ε ^ (1 / 9 : ℝ) ∧ 0 ≤ errorScale X ε A := by
  refine ⟨Real.exp 1, Real.exp_pos _, ?_⟩
  intro X hX
  have hL : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hX
  have hX1 : 1 ≤ X := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hY1 : 1 ≤ Y X ε := Real.one_le_rpow hX1 (by linarith)
  refine ⟨hL, Real.one_le_rpow hY1 (by norm_num), ?_⟩
  unfold errorScale
  positivity

#print axioms sieve_regime

end LeanLab.KumchevLiu2007.Task557d
