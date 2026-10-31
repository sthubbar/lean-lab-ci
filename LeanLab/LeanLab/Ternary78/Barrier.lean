/-
I-0086, unit U-1151, PC run 20261020T0303Z-988. T2 FRONTIER, MODEL.
Maksym Radziwiłł proposed on 2026-10-20, REPLIES.md line 37: ternary Goldbach by the
Deshouillers-Effinger-te Riele-Zinoviev GRH route, P0011 and P0097, with a zero-free half-plane
Re s > 7/8 for every Dirichlet L-function, the OpenAI quasi-Riemann claim, I-0081, in place of
GRH, so as to avoid the Helfgott-Platt check to 8.875e30.

The barrier, in log units `L = log N`. With zeros only known to lie in Re s ≤ θ, every explicit
formula error is `N^θ` times logs, so the circle method saves `N^{1−θ} = N^{1/8}` and must beat
a loss `C (log N)^k`. Zinoviev's own GRH proof, P0097 Lemma 2.1 p. 348, needs
`√N ≥ about 1925 (log N)^4`, from his term `2.75 √(Nq) log N`, `q ≤ τ = 4900 log⁴N`, against
`0.1 N / log N`; that calibration gives his 10^20. MODEL: the same losses with `N^{1/8}` give
* `calib_fails`: `exp(L/8) < 1925 L^4` for every `1 ≤ L ≤ 232`, so this route cannot close for
  any `N ≤ e^232`, about 10^100.7.
* `opt_fails`: even a loss of only `(log N)^2` with constant 1 fails for `2 ≤ L ≤ 64`,
  `N ≤ e^64`, about 6.2e27; `opt_holds72` shows it does close by `L = 72`.
So a 7/8 half-plane alone puts the analytic threshold at 10^27 or above under any plausible
loss, the range Helfgott-Platt already checked, not below the about 1.2e20 the prime gap half of
DETZ reaches under the same hypothesis, see Python in the PROGRESS line.
These are statements about real numbers only; the link to the circle method is a MODEL, not a
theorem. AI wrote this Lean code. Ternary Goldbach is a theorem, Helfgott; binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Ternary78

open Real

/-- Shared step: if `L/8 ≤ m` then `exp (L/8) < 2.7182818286 ^ m`, for `m ≥ 1`. -/
theorem exp_lt_of_le {L : ℝ} {m : ℕ} (hm : 1 ≤ m) (h : L / 8 ≤ m) :
    exp (L / 8) < 2.7182818286 ^ m := by
  have he : exp (L / 8) ≤ exp 1 ^ m := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by linarith)
  have hp : exp 1 ^ m < 2.7182818286 ^ m :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by omega)
  linarith

/-- The ceiling step: some natural `m` has `m − 1 < L/8 ≤ m`. -/
theorem ceil_step {L : ℝ} (h : 0 ≤ L) : ∃ m : ℕ, (m : ℝ) - 1 < L / 8 ∧ L / 8 ≤ m :=
  ⟨⌈L / 8⌉₊, by have := Nat.ceil_lt_add_one (show 0 ≤ L / 8 by positivity); linarith,
    Nat.le_ceil _⟩

/-- **Calibrated barrier.** Zinoviev's losses with the `N^{1/8}` saving fail up to `e^232`. -/
theorem calib_fails {L : ℝ} (h1 : 1 ≤ L) (h2 : L ≤ 232) : exp (L / 8) < 1925 * L ^ 4 := by
  obtain ⟨m, hm1, hm2⟩ := ceil_step (by linarith : (0 : ℝ) ≤ L)
  have hm : m ≤ 29 := by
    by_contra h; push_neg at h
    have : (30 : ℝ) ≤ m := by exact_mod_cast h
    linarith
  have hm0 : 1 ≤ m := by
    by_contra h; push_neg at h
    have : m = 0 := by omega
    subst this; simp at hm2; linarith
  have hE := exp_lt_of_le hm0 hm2
  have hL4 : (max 1 (8 * ((m : ℝ) - 1))) ^ 4 ≤ L ^ 4 :=
    pow_le_pow_left₀ (by positivity) (max_le h1 (by linarith)) 4
  interval_cases m <;> norm_num at hE hL4 ⊢ <;> linarith

/-- **Optimistic barrier.** A loss of `(log N)^2` with constant 1 still fails up to `e^64`. -/
theorem opt_fails {L : ℝ} (h1 : 2 ≤ L) (h2 : L ≤ 64) : exp (L / 8) < L ^ 2 := by
  obtain ⟨m, hm1, hm2⟩ := ceil_step (by linarith : (0 : ℝ) ≤ L)
  have hm : m ≤ 8 := by
    by_contra h; push_neg at h
    have : (9 : ℝ) ≤ m := by exact_mod_cast h
    linarith
  have hm0 : 1 ≤ m := by
    by_contra h; push_neg at h
    have : m = 0 := by omega
    subst this; simp at hm2; linarith
  have hE := exp_lt_of_le hm0 hm2
  have hL2 : (max 2 (8 * ((m : ℝ) - 1))) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (by positivity) (max_le h1 (by linarith)) 2
  interval_cases m <;> norm_num at hE hL2 ⊢ <;> linarith

/-- The optimistic loss is beaten by `L = 72`, `N = e^72`, about 1.9e31: the barrier is real but
finite, vacuity of the model. -/
theorem opt_holds72 : (72 : ℝ) ^ 2 < exp (72 / 8) := by
  have h : exp 1 ^ 9 = exp (72 / 8) := by rw [← Real.exp_nat_mul]; norm_num
  have hp : (2.7182818283 : ℝ) ^ 9 < exp 1 ^ 9 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  rw [← h]; norm_num at hp ⊢; linarith

/-- Calibration check: the same model with Zinoviev's GRH saving `N^{1/2}` closes at his
`N = 10^20`, `L = 20 log 10 ≥ 46`: `exp(46/2) > 1925 · 47^4` and `log 10^20 < 47`. -/
theorem grh_calibration : 1925 * (47 : ℝ) ^ 4 < exp (46 / 2) := by
  have h : exp 1 ^ 23 = exp (46 / 2) := by rw [← Real.exp_nat_mul]; norm_num
  have hp : (2.7182818283 : ℝ) ^ 23 < exp 1 ^ 23 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  rw [← h]; norm_num at hp ⊢; linarith

end LeanLab.Ternary78
