import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/1606.00869v2 page 2, Theorem 1.
This file audits the two error expressions. It does not refute either theorem.
-/

namespace LeanLab.LZCesaroShort

open Filter

/-- The printed error at H equal to one has no uniform constant bound by the legacy error.
This is an auxiliary comparison of the page 2 formula with the inherited lab reading. -/
theorem printed_error_not_uniformly_le_legacy :
    ¬ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      (N : ℝ) * Real.log (2 * (N : ℝ) / 1) ^ 2
          + 1 * Real.log N ^ 2 * Real.log (2 * 1) ≤
        K * (N * Real.log (2 * (N : ℝ) ^ 2 / 1)
          + 1 * Real.log N ^ 2 * Real.log (2 * 1)) := by
  rintro ⟨K, hK⟩
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (4 * |K| + 5))
  let N := max N₀ 2
  have hN2 : 2 ≤ N := le_max_right _ _
  have hL : 4 * |K| + 5 ≤ Real.log (N : ℝ) := hN₀ N (le_max_left _ _)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hLpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hLle : Real.log (N : ℝ) ≤ N := by
    have := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hlog2pos : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlogA : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) (ne_of_gt hNpos)
  have hlogB : Real.log (2 * (N : ℝ) ^ 2) = Real.log 2 + 2 * Real.log N := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ (ne_of_gt hNpos)), Real.log_pow]
    norm_num
  have hSq : Real.log (N : ℝ) ^ 2 ≤ N * Real.log N := by
    nlinarith [mul_le_mul_of_nonneg_right hLle hLpos.le]
  have hlegacy : (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2)
      + Real.log N ^ 2 * Real.log 2 ≤ 4 * (N * Real.log N) := by
    rw [hlogB]
    have h1 := mul_le_mul_of_nonneg_left hlog2le hNpos.le
    have h2 := mul_le_mul_of_nonneg_left hlog2le (sq_nonneg (Real.log (N : ℝ)))
    have h3 : (N : ℝ) ≤ N * Real.log N := by nlinarith [abs_nonneg K]
    nlinarith
  have hlegacy0 : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2)
      + Real.log N ^ 2 * Real.log 2 := by
    rw [hlogB]
    positivity
  have hprinted : (N : ℝ) * Real.log N ^ 2 ≤
      N * Real.log (2 * (N : ℝ)) ^ 2 + Real.log N ^ 2 * Real.log 2 := by
    rw [hlogA]
    have h1 : Real.log (N : ℝ) ^ 2 ≤ (Real.log 2 + Real.log N) ^ 2 := by
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hNpos.le
    have h3 := mul_nonneg (sq_nonneg (Real.log (N : ℝ))) hlog2pos
    linarith
  have hb := hK N hN2
  simp only [div_one, one_mul, mul_one] at hb
  have hb' : (N : ℝ) * Real.log N ^ 2 ≤ |K| * (4 * (N * Real.log N)) := by
    calc
      _ ≤ N * Real.log (2 * (N : ℝ)) ^ 2 + Real.log N ^ 2 * Real.log 2 := hprinted
      _ ≤ K * (N * Real.log (2 * (N : ℝ) ^ 2) + Real.log N ^ 2 * Real.log 2) := hb
      _ ≤ |K| * (N * Real.log (2 * (N : ℝ) ^ 2) + Real.log N ^ 2 * Real.log 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) hlegacy0
      _ ≤ |K| * (4 * (N * Real.log N)) :=
        mul_le_mul_of_nonneg_left hlegacy (abs_nonneg K)
  have hstrict : 4 * |K| < Real.log (N : ℝ) := by linarith
  have hmul := mul_lt_mul_of_pos_left hstrict (mul_pos hNpos hLpos)
  nlinarith

/-- The intermediate logarithm comparison in DecompJ330 fails at N equal to 1024 and H equal to two.
The comparison is a lab proof step, not a statement printed in the paper. -/
theorem legacy_log_comparison_counterexample :
    ¬ Real.log (2 * (1024 : ℝ) / 2) ^ 2 ≤
      2 * Real.log (2 * (1024 : ℝ) ^ 2 / 2) := by
  intro h
  have ha : 2 * (1024 : ℝ) / 2 = (2 : ℝ) ^ 10 := by norm_num
  have hb : 2 * (1024 : ℝ) ^ 2 / 2 = (2 : ℝ) ^ 20 := by norm_num
  rw [ha, hb, Real.log_pow, Real.log_pow] at h
  norm_num at h
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hl
  nlinarith

end LeanLab.LZCesaroShort
