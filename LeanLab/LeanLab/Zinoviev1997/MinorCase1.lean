/-
AI wrote this Lean code. Codex task69, 2026-10-25.
The elementary Case 1 arithmetic of Lemma 2.1, pages 347 to 348.
The pointwise display 2.9 remains cited.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.MinorPointwise

namespace LeanLab.Zinoviev1997
open Real Finset

/-- The upper remainder in display 2.9 is small on denominators through Q. -/
theorem minor_upper_case1 (N : ℝ) (q : ℕ) (hN : 10 ^ 20 ≤ N)
    (hq : (q : ℝ) ≤ 1.1 * Real.log N ^ 2) :
    2.75 * Real.sqrt (N * q) * Real.log N ≤ 0.01 * N / Real.log N := by
  let L := Real.log N
  have hn : 0 < N := by linarith
  have hl : 46 ≤ L := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have hl0 : 0 < L := by linarith
  have he : Real.exp (L / 2) = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
    congr 1
    ring
  have hc := cube_lt_exp_sharp L hl
  rw [he] at hc
  have hs : Real.sqrt q ≤ 1.1 * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · change (q : ℝ) ≤ 1.1 * L ^ 2 at hq
      nlinarith
  have hsq := Real.sq_sqrt hn.le
  change 2.75 * Real.sqrt (N * q) * L ≤ 0.01 * N / L
  rw [Real.sqrt_mul hn.le, le_div_iff₀ hl0]
  have h₁ := mul_le_mul_of_nonneg_left hc.le (Real.sqrt_nonneg N)
  have h₂ := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2.75 * Real.sqrt N * L ^ 2 by positivity)
  nlinarith

/-- Being outside the narrow arc bounds the leading term by 0.08 N over log N. -/
theorem minor_main_case1 (N : ℝ) (q : ℕ) (z : ℝ) (hN : 10 ^ 20 ≤ N)
    (hq : 0 < q) (hz : 2 * Real.log N / (Nat.totient q * N) ≤ |z|) :
    1 / ((Nat.totient q : ℝ) * ‖minorCoordinate N z‖) < 0.08 * N / Real.log N := by
  have hn : 0 < N := by linarith
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have h₁ := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * Real.pi * Nat.totient q by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (minorCoordinate_norm_phase N z) hφ.le
  have he : (2 * Real.pi * Nat.totient q) * (2 * Real.log N / (Nat.totient q * N)) =
      4 * Real.pi * Real.log N / N := by field_simp; ring
  rw [he] at h₁
  have hd : 4 * Real.pi * Real.log N / N ≤ (Nat.totient q : ℝ) * ‖minorCoordinate N z‖ := by
    nlinarith
  have hd0 : 0 < 4 * Real.pi * Real.log N / N := by positivity
  have hh := one_div_le_one_div_of_le hd0 hd
  have hpi : 1 / (4 * Real.pi) < (0.08 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d2]
  have hm := mul_lt_mul_of_pos_right hpi (div_pos hn hl)
  calc
    _ ≤ 1 / (4 * Real.pi * Real.log N / N) := hh
    _ = (1 / (4 * Real.pi)) * (N / Real.log N) := by field_simp
    _ < 0.08 * (N / Real.log N) := hm
    _ = _ := by ring

/-- Lemma 2.1 Case 1, CONDITIONAL ON the pointwise GRH estimate 2.9. -/
theorem lemma21_case1_of_29 (N : ℝ) (q : ℕ) (z : ℝ) (s : ℂ)
    (hN : 10 ^ 20 ≤ N) (hq : 0 < q) (hqQ : (q : ℝ) ≤ 1.1 * Real.log N ^ 2)
    (hz : 2 * Real.log N / (Nat.totient q * N) ≤ |z|) (h29 : Lemma29At N q z s) :
    ‖s‖ < 0.18 * N / Real.log N := by
  have hm := minor_main_case1 N q z hN hq hz
  have hn : 0 < N := by linarith
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hp : 0 < N / Real.log N := div_pos hn hl
  by_cases hphase : 2 * Real.pi * N * |z| ≤ 10
  · have hs := h29.1 hphase
    have he := minor_upper_case1 N q hN hqQ
    simp only [div_eq_mul_inv] at hs hm he hp ⊢
    nlinarith
  · have hs := h29.2 (lt_of_not_ge hphase)
    rw [minor_lower_error N (by linarith)] at hs
    simp only [div_eq_mul_inv] at hs hm hp ⊢
    nlinarith

end LeanLab.Zinoviev1997
