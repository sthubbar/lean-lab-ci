/-
Tao 2012, P0007, unit U-0927, run 20261018T0803Z-19871. arXiv 1201.6656 v4, the end of
Section 8, the proof of (8.18) on the arcs past the weakly major arcs, read in Claude in
Chrome, arxiv.org/html/1201.6656, 2026-10-18.

Four cases, each a printed numerical claim, checked here; the exponential sum bounds (1.9),
(1.10), (1.12) of Theorem 1.1 and Lemma 4.3 stay cited.
* `caseA`: for α ≥ 20/N₀, 1.01/(2α) ≤ 0.078 N₀/3.
* `weak_minor_le`: the weakly minor arc bracket is at most 0.021 < 0.078, MATCH; and
  `weak_minor_printed_gt`: the printed remark "in fact it is less than 0.004" is false,
  the bracket exceeds 0.017. FINDING F-0025, cosmetic.
* `inter_le`: the intermediate arc bracket is less than 0.013, MATCH.
* `strong_le`: the strongly minor arc bracket is less than 0.0002, MATCH.
Each bracket is a function of a logarithm `t`; `y^{-1/k} = exp (-t/k)` with `t = log y`.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Tao2012.MinorArcs

open Real

/-- The decay lemma used in every case: if `P (u₀ + v) ≤ M (1 + v + v²/2)` for `v ≥ 0`, then
`exp (-u) P u ≤ M / exp u₀` for `u ≥ u₀`. -/
theorem decay {P : ℝ → ℝ} {u₀ M u : ℝ} (hM : 0 ≤ M) (hu : u₀ ≤ u)
    (hP : ∀ v : ℝ, 0 ≤ v → P (u₀ + v) ≤ M * (1 + v + v ^ 2 / 2)) :
    exp (-u) * P u ≤ M / exp u₀ := by
  set v := u - u₀ with hv
  have hv0 : 0 ≤ v := by linarith
  have h1 := hP v hv0
  rw [show u₀ + v = u by ring] at h1
  have hq := quadratic_le_exp_of_nonneg hv0
  have hq0 : 0 < 1 + v + v ^ 2 / 2 := by positivity
  have he : exp u = exp u₀ * exp v := by rw [← exp_add, hv]; ring_nf
  rw [exp_neg, he, le_div_iff₀ (exp_pos _)]
  calc (exp u₀ * exp v)⁻¹ * P u * exp u₀ = P u / exp v := by
        field_simp
    _ ≤ M * (1 + v + v ^ 2 / 2) / exp v := by
        exact div_le_div_of_nonneg_right h1 (exp_pos _).le
    _ ≤ M := by
        rw [div_le_iff₀ (exp_pos _)]
        exact mul_le_mul_of_nonneg_left hq hM

theorem exp_one_gt' : (2.718 : ℝ) < exp 1 := by have := exp_one_gt_d9; linarith
theorem exp_one_lt' : exp 1 < (2.72 : ℝ) := by have := exp_one_lt_d9; linarith

/-- `exp n ≥ 2.718^n`. -/
theorem exp_nat_ge (n : ℕ) : (2.718 : ℝ) ^ n ≤ exp n := by
  rw [← exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) exp_one_gt'.le n

/-- `exp n ≤ 2.72^n`. -/
theorem exp_nat_le (n : ℕ) : exp n ≤ (2.72 : ℝ) ^ n := by
  rw [← exp_one_pow]
  exact pow_le_pow_left₀ (exp_pos 1).le exp_one_lt'.le n

/-! ## Case α ≥ 20/N₀ -/

/-- `|S₀||D| ≤ (1.01/(2α)) x/K`, and at `α ≥ 20/N₀` this is at most `0.078 (N₀/3) x/K`. -/
theorem caseA {α : ℝ} (hα : 20 / 4e14 ≤ α) : 1.01 / (2 * α) ≤ 0.078 * (4e14 / 3) := by
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ## Weakly minor arcs, (1.12): `1.2 y^{-1/2} log y (log y + 2.4)` at `y ≥ T₀/π` -/

/-- `log (T₀/π) ≥ 20.5`, from `e^{20.5} ≤ 2.72^20 · 2 < 3.29e9/3.15`. -/
theorem log_T0pi_ge : (20.5 : ℝ) ≤ log (3.29e9 / π) := by
  have hp := pi_lt_d2
  have hpos : 0 < 3.29e9 / π := by positivity
  rw [le_log_iff_exp_le hpos]
  have h1 : exp 20.5 = exp (20 : ℕ) * exp 0.5 := by rw [← exp_add]; norm_num
  have h2 := exp_nat_le 20
  have h3 : exp 0.5 ≤ 2 := by
    have := exp_bound_div_one_sub_of_interval' (show (0 : ℝ) < 0.5 by norm_num)
      (show (0.5 : ℝ) < 1 by norm_num)
    norm_num at this ⊢; linarith
  have h4 : exp (20 : ℕ) * exp 0.5 ≤ 2.72 ^ 20 * 2 :=
    mul_le_mul h2 h3 (exp_pos _).le (by positivity)
  rw [h1, le_div_iff₀ pi_pos]
  calc exp (20 : ℕ) * exp 0.5 * π ≤ 2.72 ^ 20 * 2 * 3.15 :=
        mul_le_mul h4 hp.le pi_pos.le (by positivity)
    _ ≤ 3.29e9 := by norm_num

theorem log_T0pi_le : log (3.29e9 / π) ≤ (20.8 : ℝ) := by
  have hp := pi_gt_d2
  have hpos : 0 < 3.29e9 / π := by positivity
  rw [log_le_iff_le_exp hpos]
  have h1 : exp 20.8 = exp (20 : ℕ) * exp 0.8 := by rw [← exp_add]; norm_num
  have h2 := exp_nat_ge 20
  have h3 : (2.19 : ℝ) ≤ exp 0.8 := by
    have h := quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.4 by norm_num)
    have e : exp 0.8 = exp 0.4 * exp 0.4 := by rw [← exp_add]; norm_num
    rw [e]; nlinarith
  have h4 : (2.718 : ℝ) ^ 20 * 2.19 ≤ exp (20 : ℕ) * exp 0.8 :=
    mul_le_mul h2 h3 (by norm_num) (exp_pos _).le
  rw [h1, div_le_iff₀ pi_pos]
  calc (3.29e9 : ℝ) ≤ 2.718 ^ 20 * 2.19 * 3.14 := by norm_num
    _ ≤ exp (20 : ℕ) * exp 0.8 * π := mul_le_mul h4 hp.le (by norm_num) (by positivity)

/-- The weakly minor bracket, second term, for every `t = log y ≥ 20.5`:
`1.2 exp(-t/2) t (t + 2.4) ≤ 0.021`. Since `x/(Kq) ≥ T₀/π`, `t ≥ log (T₀/π) ≥ 20.5`. -/
theorem weak_second_le {t : ℝ} (ht : 20.5 ≤ t) :
    1.2 * (exp (-(t / 2)) * (t * (t + 2.4))) ≤ 0.021 := by
  have key : exp (-(t / 2)) * (fun s => 2 * s * (2 * s + 2.4)) (t / 2) ≤ 470 / exp 10.25 :=
    decay (P := fun s => 2 * s * (2 * s + 2.4)) (u₀ := 10.25) (M := 470) (by norm_num) (by linarith)
      (fun v hv => by nlinarith)
  simp only at key
  have hs : 2 * (t / 2) * (2 * (t / 2) + 2.4) = t * (t + 2.4) := by ring
  rw [hs] at key
  have he : (27500 : ℝ) ≤ exp 10.25 := by
    have h1 : exp 10.25 = exp (10 : ℕ) * exp 0.25 := by rw [← exp_add]; norm_num
    have h2 := exp_nat_ge 10
    have h3 : (1.25 : ℝ) ≤ exp 0.25 := by have := add_one_le_exp (0.25 : ℝ); linarith
    rw [h1]; nlinarith [exp_pos (0.25 : ℝ)]
  have : 470 / exp 10.25 ≤ 470 / 27500 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
  linarith

/-- The first term `9.73 (π/T₀)² log² x` with `log x ≤ 3100` is below `10^{-9}`. -/
theorem weak_first_le {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 3100) :
    9.73 * (π / 3.29e9) ^ 2 * L ^ 2 ≤ 1e-9 := by
  have hp := pi_lt_d2
  have h1 : (π / 3.29e9) ^ 2 ≤ (3.15 / 3.29e9) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity); gcongr
  have h2 : L ^ 2 ≤ 3100 ^ 2 := pow_le_pow_left₀ hL0 hL 2
  calc 9.73 * (π / 3.29e9) ^ 2 * L ^ 2 ≤ 9.73 * (3.15 / 3.29e9) ^ 2 * 3100 ^ 2 := by
        gcongr
    _ ≤ 1e-9 := by norm_num

/-- MATCH: the weakly minor bracket is below `0.078`. -/
theorem weak_minor_le {L t : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 3100) (ht : 20.5 ≤ t) :
    9.73 * (π / 3.29e9) ^ 2 * L ^ 2 + 1.2 * (exp (-(t / 2)) * (t * (t + 2.4))) ≤ 0.078 := by
  linarith [weak_first_le hL0 hL, weak_second_le ht]

/-- FINDING F-0025, cosmetic: the printed bracket
`9.73 (π/T₀)² log² x + 1.19 √π/√T₀ log(T₀/π)(log(T₀/π) + 2.3)` is above `0.017`, so the
remark "in fact it is less than 0.004" is false; the bound 0.078 the proof needs holds. -/
theorem weak_minor_printed_gt :
    0.017 < 1.19 * (sqrt π / sqrt 3.29e9) * log (3.29e9 / π) * (log (3.29e9 / π) + 2.3) := by
  have hl := log_T0pi_ge
  have hp := pi_gt_d2
  have hs : (3.08e-5 : ℝ) ≤ sqrt π / sqrt 3.29e9 := by
    rw [← sqrt_div' π (by norm_num : (0:ℝ) ≤ 3.29e9)]
    rw [le_sqrt (by norm_num) (by positivity)]
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have h1 : (0.017 : ℝ) < 1.19 * 3.08e-5 * 20.5 * (20.5 + 2.3) := by norm_num
  have h2 : 1.19 * 3.08e-5 * 20.5 * (20.5 + 2.3) ≤
      1.19 * (sqrt π / sqrt 3.29e9) * log (3.29e9 / π) * (log (3.29e9 / π) + 2.3) := by
    gcongr
  linarith

/-! ## Intermediate arcs, (1.9): `(0.8 y^{-1/6} + 0.15 y^{-1/5}) log y (log y + 11.3)` -/

/-- `log (8.7e33) ≥ 78`, from `e^78 ≤ 2.72^78 < 8.7e33`. -/
theorem log_y_ge {y : ℝ} (hy : 8.7e33 ≤ y) : (78 : ℝ) ≤ log y := by
  have hy0 : 0 < y := by linarith
  rw [le_log_iff_exp_le hy0]
  have := exp_nat_le 78
  have h2 : (2.72 : ℝ) ^ 78 ≤ 8.7e33 := by norm_num
  push_cast at this
  linarith

/-- MATCH: for every `t ≥ 78` the intermediate bracket is below `0.013`. -/
theorem inter_le {t : ℝ} (ht : 78 ≤ t) :
    (0.8 * exp (-(t / 6)) + 0.15 * exp (-(t / 5))) * (t * (t + 11.3)) ≤ 0.013 := by
  have key : exp (-(t / 6)) * (fun s => 6 * s * (6 * s + 11.3)) (t / 6) ≤ 6966 / exp 13 :=
    decay (P := fun s => 6 * s * (6 * s + 11.3)) (u₀ := 13) (M := 6966) (by norm_num) (by linarith)
      (fun v hv => by nlinarith)
  simp only at key
  have hs : 6 * (t / 6) * (6 * (t / 6) + 11.3) = t * (t + 11.3) := by ring
  rw [hs] at key
  have he : (441000 : ℝ) ≤ exp 13 := by
    have := exp_nat_ge 13; push_cast at this
    have h : (441000 : ℝ) ≤ 2.718 ^ 13 := by norm_num
    linarith
  have hk : exp (-(t / 6)) * (t * (t + 11.3)) ≤ 0.0158 := by
    have : 6966 / exp 13 ≤ 6966 / 441000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
    have : (6966 : ℝ) / 442000 ≤ 0.0158 := by norm_num
    linarith
  have h5 : exp (-(t / 5)) ≤ 0.1 * exp (-(t / 6)) := by
    have : exp (-(t / 5)) = exp (-(t / 6)) * exp (-(t / 30)) := by rw [← exp_add]; ring_nf
    rw [this]
    have h30 : exp (-(t / 30)) ≤ 0.1 := by
      have hm : exp (-(t / 30)) ≤ exp (-2.6) := exp_le_exp.mpr (by linarith)
      have h26 : (10 : ℝ) ≤ exp 2.6 := by
        have h1 : exp 2.6 = exp (2 : ℕ) * exp 0.6 := by rw [← exp_add]; norm_num
        have h2 := exp_nat_ge 2
        have h3 : (1.6 : ℝ) ≤ exp 0.6 := by have := add_one_le_exp (0.6 : ℝ); linarith
        rw [h1]; nlinarith [exp_pos (0.6 : ℝ)]
      have : exp (-2.6) ≤ 0.1 := by
        rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]; linarith
      linarith
    nlinarith [exp_pos (-(t / 6))]
  have hT : 0 ≤ t * (t + 11.3) := by nlinarith
  have hE := exp_pos (-(t / 6))
  nlinarith

/-! ## Strongly minor arcs, (1.10) -/

/-- `log q ≥ 29` for `q ≥ 5·10^12 - 1`, from `e^29 ≤ 2.72^29 < 5·10^12 - 1`. -/
theorem log_q_ge {q : ℝ} (hq : 5e12 - 1 ≤ q) : (29 : ℝ) ≤ log q := by
  have hq0 : 0 < q := by linarith
  rw [le_log_iff_exp_le hq0]
  have := exp_nat_le 29
  have h2 : (2.72 : ℝ) ^ 29 ≤ 5e12 - 1 := by norm_num
  push_cast at this
  linarith

/-- MATCH: with `log (2x/K) ≤ 3100` and `q ≥ N₀/80 - 1`, the strongly minor bracket
`0.5 (1/q) L (L + 15) + 0.31 q^{-1/2} log q (log q + 8.9)` is below `0.0002`; written with
`ℓ = log q` and `q^{-1/2} = exp(-ℓ/2)`. -/
theorem strong_le {q L ℓ : ℝ} (hq : 5e12 - 1 ≤ q) (hL0 : 0 ≤ L) (hL : L ≤ 3100)
    (hℓ : 29 ≤ ℓ) :
    0.5 * (1 / q) * (L * (L + 15)) + 0.31 * (exp (-(ℓ / 2)) * (ℓ * (ℓ + 8.9))) ≤ 0.0002 := by
  have key : exp (-(ℓ / 2)) * (fun s => 2 * s * (2 * s + 8.9)) (ℓ / 2) ≤ 1100 / exp 14.5 :=
    decay (P := fun s => 2 * s * (2 * s + 8.9)) (u₀ := 14.5) (M := 1100) (by norm_num) (by linarith)
      (fun v hv => by nlinarith)
  simp only at key
  have hs : 2 * (ℓ / 2) * (2 * (ℓ / 2) + 8.9) = ℓ * (ℓ + 8.9) := by ring
  rw [hs] at key
  have he : (1.8e6 : ℝ) ≤ exp 14.5 := by
    have h1 : exp 14.5 = exp (14 : ℕ) * exp 0.5 := by rw [← exp_add]; norm_num
    have h2 := exp_nat_ge 14
    have h3 : (1.5 : ℝ) ≤ exp 0.5 := by have := add_one_le_exp (0.5 : ℝ); linarith
    have h4 : (1.8e6 : ℝ) ≤ 2.718 ^ 14 * 1.5 := by norm_num
    rw [h1]; nlinarith [exp_pos (0.5 : ℝ)]
  have hk : exp (-(ℓ / 2)) * (ℓ * (ℓ + 8.9)) ≤ 6.12e-4 := by
    have : 1100 / exp 14.5 ≤ 1100 / 1.8e6 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
    have : (1100 : ℝ) / 1.8e6 ≤ 6.12e-4 := by norm_num
    linarith
  have hq0 : 0 < q := by linarith
  have h1 : 1 / q ≤ 1 / (5e12 - 1) := one_div_le_one_div_of_le (by norm_num) hq
  have h2 : L * (L + 15) ≤ 3100 * 3115 := by nlinarith
  have h3 : 0.5 * (1 / q) * (L * (L + 15)) ≤ 0.5 * (1 / (5e12 - 1)) * (3100 * 3115) := by
    have : 0 ≤ 1 / q := by positivity
    have : 0 ≤ L * (L + 15) := by nlinarith
    gcongr
  have h4 : (0.5 : ℝ) * (1 / (5e12 - 1)) * (3100 * 3115) ≤ 1e-6 := by norm_num
  nlinarith

/-- `N₀/80 - 1 = 5·10^12 - 1`, as printed. -/
theorem N0_80 : (4e14 : ℝ) / 80 - 1 = 5e12 - 1 := by norm_num

#print axioms decay
#print axioms caseA
#print axioms log_T0pi_ge
#print axioms log_T0pi_le
#print axioms weak_second_le
#print axioms weak_first_le
#print axioms weak_minor_le
#print axioms weak_minor_printed_gt
#print axioms log_y_ge
#print axioms inter_le
#print axioms log_q_ge
#print axioms strong_le
#print axioms N0_80

end LeanLab.Tao2012.MinorArcs
