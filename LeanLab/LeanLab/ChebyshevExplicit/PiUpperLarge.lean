/-
AI wrote the Lean code. Codex task04, 2026-10-21.
A simple large-input corollary of the explicit quadratic pi bound.
The only inputs are local proofs and Mathlib's exponential Taylor bound.
Goldbach is open.
-/
import LeanLab.ChebyshevExplicit.PiUpperQuadratic

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- A large-input pi bound derived without a cited Dusart hypothesis. -/
theorem pi_exp_le_five_fourths (L : ℝ) (hL : 32 ≤ L) :
    (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤ 1.25 * exp L / L := by
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < exp L := exp_pos _
  have hs0 : 0 < exp (L / 2) := exp_pos _
  have hx4 : 4 ≤ exp L := by linarith [add_one_le_exp L]
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
  have hL5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hL 5
  have hL6a : (32 : ℝ) ^ 5 * L ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hL5 hL0.le
    nlinarith only [h]
  have hLS : L ≤ (3 / 2000 : ℝ) * exp (L / 2) := by
    norm_num at hL6a
    nlinarith only [hL6a, hse, hL]
  have hroot : exp (L / 2) * L ≤ (3 / 2000 : ℝ) * exp L := by
    have h := mul_le_mul_of_nonneg_left hLS hs0.le
    nlinarith only [h, hsquare]
  have hL4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hL 4
  have hL6b : (32 : ℝ) ^ 4 * L ^ 2 ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hL4 (sq_nonneg L)
    nlinarith only [h]
  have hL2 : L ^ 2 ≤ (7 / 10000 : ℝ) * exp L := by
    norm_num at hL6b
    nlinarith only [hL6b, he, sq_nonneg L]
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
  have herrL : E * L ≤ 0.0021 * exp L := by
    have h := mul_le_mul_of_nonneg_right herr hL0.le
    nlinarith only [h, hL2]
  have hsec : 4.42224 * exp L / L ≤ 0.138195 * exp L := by
    rw [div_le_iff₀ hL0]
    have h := mul_le_mul_of_nonneg_right hL hx0.le
    nlinarith only [h]
  have hrootTerm : 1.10556 * exp (L / 2) / log 2 ^ 2 * L ≤ 0.003731265 * exp L := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hlog2pos)]
    have h := mul_le_mul_of_nonneg_left hlog2sq
      (by positivity : 0 ≤ (0.003731265 : ℝ) * exp L)
    nlinarith only [hroot, h]
  have hp := pi_le_110556_quadratic_real hx4
  simp only [log_exp, hsqrt] at hp
  have hp' : (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤
      1.10556 * exp L / L + 4.42224 * exp L / L ^ 2
        + 1.10556 * exp (L / 2) / log 2 ^ 2 + E := by
    dsimp [E]
    linarith only [hp]
  rw [le_div_iff₀ hL0]
  calc
    _ ≤ (1.10556 * exp L / L + 4.42224 * exp L / L ^ 2
        + 1.10556 * exp (L / 2) / log 2 ^ 2 + E) * L :=
      mul_le_mul_of_nonneg_right hp' hL0.le
    _ = 1.10556 * exp L + 4.42224 * exp L / L
        + 1.10556 * exp (L / 2) / log 2 ^ 2 * L + E * L := by
      field_simp [hL0.ne', hlog2pos.ne']
    _ ≤ _ := by nlinarith only [hsec, hrootTerm, herrL, hx0]

/-- An alternative explicit split with a smaller secondary coefficient. -/
theorem pi_exp_le_two_thirds_split (L : ℝ) (hL : 3 ≤ L) :
    (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤
      1.10556 * exp L / L + 2.48751 * exp L / L ^ 2
        + 1.10556 * exp (2 * L / 3) / log 2 ^ 2
        + 5 / (2 * log 6) * L - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log L - log (log 2)) := by
  have hL0 : 0 < L := by linarith
  have hy : 2 ≤ exp (2 * L / 3) := by linarith [add_one_le_exp (2 * L / 3)]
  have hyx : exp (2 * L / 3) ≤ exp L := exp_le_exp.mpr (by linarith)
  have hp := pi_le_110556_split hy hyx
  simp only [log_exp] at hp
  have hfirst : (exp (2 * L / 3) - 2) / log 2 ^ 2 ≤ exp (2 * L / 3) / log 2 ^ 2 := by
    gcongr
    linarith
  have hsecond : (exp L - exp (2 * L / 3)) / (2 * L / 3) ^ 2 ≤
      exp L / (2 * L / 3) ^ 2 := by
    exact div_le_div_of_nonneg_right (by linarith [exp_pos (2 * L / 3)]) (sq_nonneg _)
  have hsecond' : exp L / (2 * L / 3) ^ 2 = 9 / 4 * exp L / L ^ 2 := by
    field_simp
    norm_num
  rw [hsecond'] at hsecond
  have hi := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
    (by norm_num : (0 : ℝ) ≤ 1.10556)
  have heq : 1.10556 * (exp (2 * L / 3) / log 2 ^ 2 + 9 / 4 * exp L / L ^ 2) =
      2.48751 * exp L / L ^ 2 + 1.10556 * exp (2 * L / 3) / log 2 ^ 2 := by ring
  rw [heq] at hi
  linarith only [hp, hi]

/-- The two-thirds split lowers the elementary exponential threshold to 24. -/
theorem pi_exp_le_five_fourths_24 (L : ℝ) (hL : 24 ≤ L) :
    (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤ 1.25 * exp L / L := by
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < exp L := exp_pos _
  have he8 : (2000 : ℝ) ≤ exp 8 := by
    have h : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) h 8
    rw [← exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  have hexp : exp 8 * exp ((L - 24) / 3) = exp (L / 3) := by
    rw [← exp_add]
    congr 1
    ring
  have hlinear : L ≤ (3 / 250 : ℝ) * exp (L / 3) := by
    have ht := add_one_le_exp ((L - 24) / 3)
    have hm := mul_le_mul he8 ht (by linarith : 0 ≤ (L - 24) / 3 + 1)
      (exp_pos 8).le
    rw [hexp] at hm
    linarith
  have hproduct : exp (2 * L / 3) * exp (L / 3) = exp L := by
    rw [← exp_add]
    congr 1
    ring
  have hroot : exp (2 * L / 3) * L ≤ (3 / 250 : ℝ) * exp L := by
    have h := mul_le_mul_of_nonneg_left hlinear (exp_pos (2 * L / 3)).le
    nlinarith only [h, hproduct]
  have he := pow_div_factorial_le_exp L hL0.le 6
  norm_num at he
  have hL4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 24) hL 4
  have hL6 : (24 : ℝ) ^ 4 * L ^ 2 ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hL4 (sq_nonneg L)
    nlinarith only [h]
  have hL2 : L ^ 2 ≤ (11 / 5000 : ℝ) * exp L := by
    norm_num at hL6
    nlinarith only [hL6, he, sq_nonneg L]
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
  have herrL : E * L ≤ 0.0066 * exp L := by
    have h := mul_le_mul_of_nonneg_right herr hL0.le
    nlinarith only [h, hL2]
  have hsec : 2.48751 * exp L / L ≤ 0.10364625 * exp L := by
    rw [div_le_iff₀ hL0]
    have h := mul_le_mul_of_nonneg_right hL hx0.le
    nlinarith only [h]
  have hrootTerm : 1.10556 * exp (2 * L / 3) / log 2 ^ 2 * L ≤ 0.02985012 * exp L := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hlog2pos)]
    have h := mul_le_mul_of_nonneg_left hlog2sq
      (by positivity : 0 ≤ (0.02985012 : ℝ) * exp L)
    nlinarith only [hroot, h]
  have hp := pi_exp_le_two_thirds_split L (by linarith)
  have hp' : (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤
      1.10556 * exp L / L + 2.48751 * exp L / L ^ 2
        + 1.10556 * exp (2 * L / 3) / log 2 ^ 2 + E := by
    dsimp [E]
    linarith only [hp]
  rw [le_div_iff₀ hL0]
  calc
    _ ≤ (1.10556 * exp L / L + 2.48751 * exp L / L ^ 2
        + 1.10556 * exp (2 * L / 3) / log 2 ^ 2 + E) * L :=
      mul_le_mul_of_nonneg_right hp' hL0.le
    _ = 1.10556 * exp L + 2.48751 * exp L / L
        + 1.10556 * exp (2 * L / 3) / log 2 ^ 2 * L + E * L := by
      field_simp [hL0.ne', hlog2pos.ne']
    _ ≤ _ := by nlinarith only [hsec, hrootTerm, herrL, hx0]

/-- The factor 1.25 bound at a positive real input. -/
theorem pi_le_five_fourths_of_log {x : ℝ} (hx : 0 < x) (hlog : 24 ≤ log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 1.25 * x / log x := by
  simpa only [exp_log hx] using pi_exp_le_five_fourths_24 (log x) hlog

/-- The factor 1.25 bound at a natural input. -/
theorem pi_le_five_fourths_nat (n : ℕ) (hn : 0 < n) (hlog : 24 ≤ log (n : ℝ)) :
    (Nat.primeCounting n : ℝ) ≤ 1.25 * n / log n := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  simpa only [Nat.floor_natCast] using pi_le_five_fourths_of_log hx hlog

end LeanLab.ChebyshevExplicit
