/-
AI wrote the Lean code. Codex task04, 2026-10-22.
An explicit asymptotic corollary of the quadratic pi bound.
The constants are derived from local proofs. Goldbach is open.
-/
import LeanLab.ChebyshevExplicit.PiUpperLarge

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- Absorb the lower-order terms into a single reciprocal-log correction. -/
theorem pi_exp_le_110556_add_five_div (L : ℝ) (hL : 32 ≤ L) :
    (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤ (1.10556 + 5 / L) * exp L / L := by
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < exp L := exp_pos _
  have hs0 : 0 < exp (L / 2) := exp_pos _
  have hsquare : exp (L / 2) ^ 2 = exp L := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hsqrt : (exp L).sqrt = exp (L / 2) := by
    rw [← hsquare, sqrt_sq_eq_abs, abs_of_pos hs0]
  have he := pow_div_factorial_le_exp L hL0.le 6
  norm_num at he
  have hse := pow_div_factorial_le_exp (L / 2) (by linarith : 0 ≤ L / 2) 6
  norm_num [div_pow] at hse
  have hL4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hL 4
  have hL6a : (32 : ℝ) ^ 4 * L ^ 2 ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hL4 (sq_nonneg L)
    nlinarith only [h]
  have hLS : L ^ 2 ≤ (1 / 12 : ℝ) * exp (L / 2) := by
    norm_num at hL6a
    nlinarith only [hL6a, hse, sq_nonneg L]
  have hroot : exp (L / 2) * L ^ 2 ≤ (1 / 12 : ℝ) * exp L := by
    have h := mul_le_mul_of_nonneg_left hLS hs0.le
    nlinarith only [h, hsquare]
  have hL3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hL 3
  have hL6b : (32 : ℝ) ^ 3 * L ^ 3 ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hL3 (by positivity : 0 ≤ L ^ 3)
    nlinarith only [h]
  have hLcube : L ^ 3 ≤ (1 / 30 : ℝ) * exp L := by
    norm_num at hL6b
    nlinarith only [hL6b, he, (show 0 ≤ L ^ 3 by positivity)]
  have hlog2pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2 : (2 / 3 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hlog2sq : (4 / 9 : ℝ) ≤ log 2 ^ 2 := by
    nlinarith only [hlog2, sq_nonneg (log (2 : ℝ) - 2 / 3)]
  have h6pos : 0 < log (6 : ℝ) := log_pos (by norm_num)
  have h6raw : (5 : ℝ) / 2 * log 2 ≤ log 6 :=
    log_ge_of_pow 6 5 2 (by norm_num) (by norm_num)
  have h6lower : (5 / 3 : ℝ) ≤ log 6 := by linarith
  have hb2 : (5 : ℝ) / (2 * log 6) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hinv2 : (1 : ℝ) / log 2 ≤ 3 / 2 := by
    rw [div_le_iff₀ hlog2pos]
    linarith
  have hll2 : -1 ≤ log (log (2 : ℝ)) := by
    have h := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / log 2)
    rw [log_div (by norm_num : (1 : ℝ) ≠ 0) hlog2pos.ne', log_one] at h
    linarith
  let E : ℝ := 5 / (2 * log 6) * L - 5 / (4 * log 6) * log 2
    + 5 / 4 * (1 + log L - log (log 2))
  have herr : E ≤ 3 * L := by
    have hbl := mul_le_mul_of_nonneg_right hb2 hL0.le
    have hneg : 0 ≤ (5 : ℝ) / (4 * log 6) * log 2 := by positivity
    have hlogL := log_le_sub_one_of_pos hL0
    dsimp [E]
    linarith
  have herrL : E * L ^ 2 ≤ 0.1 * exp L := by
    have h := mul_le_mul_of_nonneg_right herr (sq_nonneg L)
    nlinarith only [h, hLcube]
  have hrootTerm : 1.10556 * exp (L / 2) / log 2 ^ 2 * L ^ 2 ≤ 0.21 * exp L := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hlog2pos)]
    have h := mul_le_mul_of_nonneg_left hlog2sq
      (by positivity : 0 ≤ (0.21 : ℝ) * exp L)
    nlinarith only [hroot, h, hx0]
  have hp := pi_le_110556_quadratic_real (x := exp L) (by linarith [add_one_le_exp L])
  simp only [log_exp, hsqrt] at hp
  have hp' : (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤
      1.10556 * exp L / L + 4.42224 * exp L / L ^ 2
        + 1.10556 * exp (L / 2) / log 2 ^ 2 + E := by
    dsimp [E]
    linarith only [hp]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hL0)).mp
  calc
    _ ≤ (1.10556 * exp L / L + 4.42224 * exp L / L ^ 2
        + 1.10556 * exp (L / 2) / log 2 ^ 2 + E) * L ^ 2 :=
      mul_le_mul_of_nonneg_right hp' (sq_nonneg L)
    _ = 1.10556 * exp L * L + 4.42224 * exp L
        + 1.10556 * exp (L / 2) / log 2 ^ 2 * L ^ 2 + E * L ^ 2 := by
      field_simp [hL0.ne', hlog2pos.ne']
    _ ≤ (1.10556 + 5 / L) * exp L / L * L ^ 2 := by
      have heq : (1.10556 + 5 / L) * exp L / L * L ^ 2 =
          1.10556 * exp L * L + 5 * exp L := by field_simp
      rw [heq]
      nlinarith only [hrootTerm, herrL, hx0]

/-- An explicit threshold for every coefficient above 1.10556. -/
theorem pi_exp_le_110556_add_epsilon (ε L : ℝ) (hε : 0 < ε)
    (hL : max 32 (5 / ε) ≤ L) :
    (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤ (1.10556 + ε) * exp L / L := by
  have h32 : (32 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hthreshold : 5 / ε ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hcorrection : 5 / L ≤ ε := by
    rw [div_le_iff₀ hL0]
    have h := (div_le_iff₀ hε).mp hthreshold
    nlinarith only [h]
  apply (pi_exp_le_110556_add_five_div L h32).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 1.10556 + 5 / L ≤ 1.10556 + ε)
      (exp_pos L).le) hL0.le

end LeanLab.ChebyshevExplicit
