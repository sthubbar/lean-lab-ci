/-
Schoenfeld 1976, Math. Comp. 30, pp. 337-360, Theorem 10: the RH bounds (6.1), θ half,
and (6.3) for the Chebyshev function θ, split into the cited steps of its proof on
pp. 337-339.

* (6.11): the RH bound for ψ with the constant α₅ of (6.12): HARD leaf.
* The value α₅(23·10⁸) > 3.292 used after (6.14): MEDIUM numerical leaf.
  The value α₅(e¹⁶) > 2.02 used on p. 339: PROVED.
* [10, (3.39)] = Rosser-Schoenfeld 1962 Corollary of Theorem 14, ψ - θ < 1.02√x + 3x^{1/3},
  used in (6.13): MEDIUM leaf.
* [10, Theorem 18], display (4.5), and [10, Theorem 19], display (4.6), used in (6.15)
  and after (6.16): MEDIUM numerical leaves.
* The Rosser-Walker tables for 599 ≤ x < 1200, cited after (6.16): MEDIUM numerical leaf.

Proved glue: (6.13) from (6.11) and [10, (3.39)] with the explicit numbers of the
paper, giving (6.1) for x ≥ 23·10⁸ and (6.3) for x ≥ e¹⁶; and (6.15), (6.16) and the
upper bound θ(x) < x, giving (6.3) for 599 ≤ x < e¹⁶.

AI wrote this Lean code, Claude, ROUTE BURST S70 burst-20261122, unit thm10_split.
Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.BS2022GRH.SchoenfeldThm10S70
open Real

noncomputable section

/-- Schoenfeld 1976 displays (6.7), (6.8), (6.10) and (6.12): the constant `α₅` as a
function of `ξ`, with `α₁ = log² ξ / (π √ξ)`, `α₂ = log ξ / (π √ξ)`,
`δ₁ = α₂ (1 + α₂) / (2 + α₂)`, `α₃ = 2 log log ξ - 2 (1 + δ₁)`,
`α₄ = 2 α₃ - (α₃² + 4.152828) / log ξ` and
`α₅ = α₄ - α₁/2 - 4 - 8π log(2π) / (√ξ log ξ)`. -/
def alpha5 (ξ : ℝ) : ℝ :=
  let a1 := log ξ ^ 2 / (π * √ξ)
  let a2 := log ξ / (π * √ξ)
  let d1 := a2 * (1 + a2) / (2 + a2)
  let a3 := 2 * log (log ξ) - 2 * (1 + d1)
  let a4 := 2 * a3 - (a3 ^ 2 + 4.152828) / log ξ
  a4 - a1 / 2 - 4 - 8 * π * log (2 * π) / (√ξ * log ξ)

/-! ### Cited leaves -/

/-- LEAF: Schoenfeld 1976 display (6.11), from (6.6) to (6.10) with Lemmas 8 and 9 of
Rosser-Schoenfeld 1975 at m = 1. HARD.
Under RH, for `x ≥ ξ ≥ 82800`, `|ψ(x) - x|/x < (log x)(log x - α₅)/(8π√x)`. -/
theorem display_6_11 : RiemannHypothesis → ∀ ξ x : ℝ, 82800 ≤ ξ → ξ ≤ x →
    |Chebyshev.psi x - x| / x < log x * (log x - alpha5 ξ) / (8 * π * √x) := by
  sorry

/-- PROVED: Taylor upper bound for `exp` on `[0, 1]`, from `Real.exp_bound`. -/
theorem exp_upper (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    exp x ≤ ∑ i ∈ Finset.range 10, x ^ i / (Nat.factorial i) + x ^ 10 * (11 / (Nat.factorial 10 * 10)) := by
  have h := Real.exp_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx) (n := 10) (by norm_num)
  rw [abs_of_nonneg hx0] at h
  have := (abs_le.1 h).2
  push_cast at this ⊢
  linarith

/-- PROVED: Taylor lower bound for `exp` on `[0, 1]`, from `Real.exp_bound`. -/
theorem exp_lower (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    ∑ i ∈ Finset.range 10, x ^ i / (Nat.factorial i) - x ^ 10 * (11 / (Nat.factorial 10 * 10)) ≤ exp x := by
  have h := Real.exp_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx) (n := 10) (by norm_num)
  rw [abs_of_nonneg hx0] at h
  have := (abs_le.1 h).1
  push_cast at this ⊢
  linarith

/-- PROVED: `21.5561 ≤ log (23·10⁸)`. -/
theorem logxi_ge : (21.5561 : ℝ) ≤ log (23 * 10 ^ 8) := by
  rw [le_log_iff_exp_le (by norm_num), show (21.5561 : ℝ) = (21 : ℕ) + 0.5561 by norm_num,
    exp_add, ← exp_one_pow]
  have h1 := exp_one_lt_d9
  have h2 := exp_upper 0.5561 (by norm_num) (by norm_num)
  have h3 : exp 1 ^ 21 ≤ (2.7182818286 : ℝ) ^ 21 := pow_le_pow_left₀ (exp_pos 1).le h1.le 21
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have h4 := mul_le_mul h3 h2 (exp_pos _).le (by positivity)
  norm_num at h4 ⊢
  linarith

/-- PROVED: `log (23·10⁸) ≤ 21.5563`. -/
theorem logxi_le : log (23 * 10 ^ 8) ≤ (21.5563 : ℝ) := by
  rw [log_le_iff_le_exp (by norm_num), show (21.5563 : ℝ) = (21 : ℕ) + 0.5563 by norm_num,
    exp_add, ← exp_one_pow]
  have h1 := exp_one_gt_d9
  have h2 := exp_lower 0.5563 (by norm_num) (by norm_num)
  have h3 : (2.7182818283 : ℝ) ^ 21 ≤ exp 1 ^ 21 := pow_le_pow_left₀ (by norm_num) h1.le 21
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have h4 := mul_le_mul h3 h2 (by norm_num) (by positivity)
  norm_num at h4 ⊢
  linarith

/-- PROVED: `3.07056 ≤ log log (23·10⁸) ≤ 3.0707`. -/
theorem loglogxi_bounds : (3.07056 : ℝ) ≤ log (log (23 * 10 ^ 8)) ∧
    log (log (23 * 10 ^ 8)) ≤ (3.0707 : ℝ) := by
  have hL1 := logxi_ge
  have hL2 := logxi_le
  have hL0 : 0 < log (23 * 10 ^ 8 : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  constructor
  · rw [le_log_iff_exp_le hL0, show (3.07056 : ℝ) = (3 : ℕ) + 0.07056 by norm_num,
      exp_add, ← exp_one_pow]
    have h1 := exp_one_lt_d9
    have h2 := exp_upper 0.07056 (by norm_num) (by norm_num)
    have h3 : exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ (exp_pos 1).le h1.le 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
    have h4 := mul_le_mul h3 h2 (exp_pos _).le (by positivity)
    norm_num at h4 hL1 ⊢
    linarith
  · rw [log_le_iff_le_exp hL0, show (3.0707 : ℝ) = (3 : ℕ) + 0.0707 by norm_num,
      exp_add, ← exp_one_pow]
    have h1 := exp_one_gt_d9
    have h2 := exp_lower 0.0707 (by norm_num) (by norm_num)
    have h3 : (2.7182818283 : ℝ) ^ 3 ≤ exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
    have h4 := mul_le_mul h3 h2 (by norm_num) (by positivity)
    norm_num at h4 hL2 ⊢
    linarith

/-- Schoenfeld 1976, after (6.14): on letting `ξ = 23·10⁸`, `α₅ > α₆ > 2`;
numerically `α₅(23·10⁸) = 3.2925...`. Was a MEDIUM numerical LEAF; PROVED by S70 from
Taylor bounds for `exp` and the Mathlib bounds on `e` and `π`; interval margin about 5.6e-5. -/
theorem alpha5_23e8 : 3.292 < alpha5 (23 * 10 ^ 8) := by
  obtain ⟨hLL1, hLL2⟩ := loglogxi_bounds
  have hL1 := logxi_ge
  have hL2 := logxi_le
  have hS : (47958 : ℝ) ≤ √(23 * 10 ^ 8) := by
    rw [show (47958 : ℝ) = √(47958 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hpi := pi_gt_d2
  have hpi4 := pi_lt_d4
  have h2pi : log (2 * π) < 2 := by
    rw [log_lt_iff_lt_exp (by positivity)]
    have : (7.3 : ℝ) < exp 2 := by
      have h := exp_one_gt_d9
      have : exp 2 = exp 1 ^ 2 := by rw [← exp_nat_mul]; norm_num
      rw [this]; nlinarith
    linarith
  have h2pi0 : 0 < log (2 * π) := log_pos (by linarith)
  unfold alpha5
  dsimp only
  set L := log (23 * 10 ^ 8 : ℝ) with hL
  set LL := log L with hLLdef
  set S := √(23 * 10 ^ 8 : ℝ) with hSdef
  have hL0 : 0 < L := by linarith
  have hS0 : 0 < S := by linarith
  have hPS : 3.14 * 47958 ≤ π * S := mul_le_mul hpi.le hS (by norm_num) pi_pos.le
  set a2 := L / (π * S) with ha2
  have ha2p : 0 < a2 := by positivity
  have ha2u : a2 ≤ 0.000144 := by
    rw [ha2, div_le_iff₀ (by positivity)]; nlinarith
  have hd1 : a2 * (1 + a2) / (2 + a2) ≤ 0.0000721 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hd1p : 0 ≤ a2 * (1 + a2) / (2 + a2) := by positivity
  set a3 := 2 * LL - 2 * (1 + a2 * (1 + a2) / (2 + a2)) with ha3
  have ha3l : 4.140975 ≤ a3 := by rw [ha3]; linarith
  have ha3u : a3 ≤ 4.1414 := by rw [ha3]; linarith
  have hsq : (a3 ^ 2 + 4.152828) / L ≤ 0.98832 := by
    rw [div_le_iff₀ hL0]; nlinarith
  have ha1 : L ^ 2 / (π * S) / 2 ≤ 0.001544 := by
    rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
  have hlast : 8 * π * log (2 * π) / (S * L) ≤ 0.0000487 := by
    have hp2 : π * log (2 * π) < 3.1416 * 2 := mul_lt_mul'' hpi4 h2pi pi_pos.le h2pi0.le
    have hSL : 47958 * 21.5561 ≤ S * L := mul_le_mul hS hL1 (by norm_num) hS0.le
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- Schoenfeld 1976, p. 339 top: on letting `ξ = e¹⁶`, `α₅ > α₆ > 0`;
numerically `α₅(e¹⁶) = 2.0279...`. Was a MEDIUM numerical leaf; PROVED by S70 from
`log 2 > 0.6931471803`, `e > 2.7182818283` and `3.14 < π < 3.1416`. -/
theorem alpha5_e16 : 2.02 < alpha5 (exp 16) := by
  have hs : √(exp 16) = exp 8 := by
    rw [show (16:ℝ) = 8 + 8 by norm_num, exp_add, sqrt_mul_self (exp_pos 8).le]
  have hl : log (exp 16) = 16 := log_exp 16
  have hll : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  have hE : 2980 < exp 8 := by
    have := exp_one_gt_d9
    have h : exp 8 = exp 1 ^ 8 := by rw [← exp_nat_mul]; norm_num
    rw [h]
    have : (2.9809 : ℝ) * 1000 < 2.7182818283 ^ 8 := by norm_num
    nlinarith [pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num : (8:ℕ) ≠ 0)]
  have hL2 := log_two_gt_d9
  have hpi := pi_gt_three
  have hpi4 := pi_lt_d4
  have h2pi : log (2 * π) < 2 := by
    rw [log_lt_iff_lt_exp (by positivity)]
    have : (7.3 : ℝ) < exp 2 := by
      have h := exp_one_gt_d9
      have : exp 2 = exp 1 ^ 2 := by rw [← exp_nat_mul]; norm_num
      rw [this]; nlinarith
    linarith
  have h2pi0 : 0 < log (2 * π) := log_pos (by linarith)
  unfold alpha5
  simp only [hs, hl, hll]
  set E := exp 8
  set a2 := 16 / (π * E) with ha2
  have ha2p : 0 < a2 := by positivity
  have ha2u : a2 < 0.002 := by
    rw [ha2, div_lt_iff₀ (by positivity)]; nlinarith
  have hd1 : a2 * (1 + a2) / (2 + a2) ≤ 0.0011 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hd1p : 0 ≤ a2 * (1 + a2) / (2 + a2) := by positivity
  set a3 := 2 * (4 * log 2) - 2 * (1 + a2 * (1 + a2) / (2 + a2)) with ha3
  have ha3l : 3.5429 ≤ a3 := by rw [ha3]; linarith
  have ha3u : a3 ≤ 5.6 := by rw [ha3]; linarith [log_two_lt_d9]
  have ha4 : 6.0417 ≤ 2 * a3 - (a3 ^ 2 + 4.152828) / 16 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha3l) (sub_nonneg.mpr ha3u)]
  have hπE : 3.14 * 2980 < π * E := mul_lt_mul'' pi_gt_d2 hE (by norm_num) (by norm_num)
  have ha1 : (16:ℝ) ^ 2 / (π * E) / 2 ≤ 0.014 := by
    rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
  have hlast : 8 * π * log (2 * π) / (E * 16) ≤ 0.002 := by
    have hp2 : π * log (2 * π) < 3.1416 * 2 := mul_lt_mul'' hpi4 h2pi pi_pos.le h2pi0.le
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- LEAF: Rosser-Schoenfeld 1962 display (3.39), cited as [10, (3.39)] in Schoenfeld 1976
(6.13). MEDIUM. For `0 < x`, `ψ(x) - θ(x) < 1.02 x^{1/2} + 3 x^{1/3}`. -/
theorem rs62_3_39 : ∀ x : ℝ, 0 < x →
    Chebyshev.psi x - Chebyshev.theta x < 1.02 * √x + 3 * x ^ ((1 : ℝ) / 3) := by
  sorry

/-- LEAF: Rosser-Schoenfeld 1962 Theorem 18, display (4.5), cited as [10, Theorem 18] in
Schoenfeld 1976 before (6.15). MEDIUM numerical.
For `0 < x ≤ 10⁸`, `x - 2.05282 x^{1/2} < θ(x) < x`. -/
theorem rs62_thm18 : ∀ x : ℝ, 0 < x → x ≤ 10 ^ 8 →
    x - 2.05282 * √x < Chebyshev.theta x ∧ Chebyshev.theta x < x := by
  sorry

/-- LEAF: Rosser-Schoenfeld 1962 Theorem 19, display (4.6), cited as [10, Theorem 19] in
Schoenfeld 1976 after (6.16). MEDIUM numerical.
For `0 < x ≤ 1420.9` and for `1423 ≤ x ≤ 10⁸`, `x - 2 x^{1/2} < θ(x)`. -/
theorem rs62_thm19 : ∀ x : ℝ, (0 < x ∧ x ≤ 1420.9) ∨ (1423 ≤ x ∧ x ≤ 10 ^ 8) →
    x - 2 * √x < Chebyshev.theta x := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 339, after (6.16): for `599 ≤ x < 1200`, (6.16)
`θ(x) - x > -(√x log² x)/(8π)` follows from the unpublished Rosser-Walker tables
of [10, Section 5]. MEDIUM numerical. -/
theorem rosser_walker_599 : ∀ x : ℝ, 599 ≤ x → x < 1200 →
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x := by
  sorry

/-! ### Proved glue -/

lemma exp_one_pow_lt (n : ℕ) (hn : 0 < n) : exp (n : ℝ) < 2.7182818286 ^ n := by
  rw [← exp_one_pow]
  exact pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le hn.ne'

lemma exp_one_pow_gt (n : ℕ) (hn : 0 < n) : 2.7182818283 ^ n < exp (n : ℝ) := by
  rw [← exp_one_pow]
  exact pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) hn.ne'

/-- If `exp a ^ k < c ^ k` with `c ≤ x`, then `a ≤ log x`. -/
lemma le_log_of_pow {a c x : ℝ} (k : ℕ) (_hk : k ≠ 0) (hc : 0 < c)
    (h : exp a ^ k < c ^ k) (hx : c ≤ x) : a ≤ log x := by
  have h1 : exp a < c := lt_of_pow_lt_pow_left₀ k hc.le h
  rw [le_log_iff_exp_le (by linarith)]
  linarith

lemma log_ge_215 {x : ℝ} (hx : 23 * 10 ^ 8 ≤ x) : 21.5 ≤ log x := by
  refine le_log_of_pow 2 (by norm_num) (by norm_num) ?_ hx
  rw [← exp_nat_mul]
  have h1 := exp_one_pow_lt 43 (by norm_num)
  have h2 : (2.7182818286 : ℝ) ^ 43 < (23 * 10 ^ 8 : ℝ) ^ 2 := by norm_num
  have h3 : (((2 : ℕ) : ℝ) * 21.5) = ((43 : ℕ) : ℝ) := by norm_num
  rw [h3]
  exact h1.trans h2

lemma log_ge_72 {x : ℝ} (hx : 1400 ≤ x) : 7.2 ≤ log x := by
  refine le_log_of_pow 5 (by norm_num) (by norm_num) ?_ hx
  rw [← exp_nat_mul]
  have h1 := exp_one_pow_lt 36 (by norm_num)
  have h2 : (2.7182818286 : ℝ) ^ 36 < (1400 : ℝ) ^ 5 := by norm_num
  have h3 : (((5 : ℕ) : ℝ) * 7.2) = ((36 : ℕ) : ℝ) := by norm_num
  rw [h3]
  exact h1.trans h2

set_option exponentiation.threshold 1000 in
lemma log_ge_709 {x : ℝ} (hx : 1200 ≤ x) : 7.09 ≤ log x := by
  refine le_log_of_pow 100 (by norm_num) (by norm_num) ?_ hx
  rw [← exp_nat_mul]
  have h1 := exp_one_pow_lt 709 (by norm_num)
  have h2 : (2.7182818286 : ℝ) ^ 709 < (1200 : ℝ) ^ 100 := by norm_num
  have h3 : (((100 : ℕ) : ℝ) * 7.09) = ((709 : ℕ) : ℝ) := by norm_num
  rw [h3]
  exact h1.trans h2

lemma exp16_gt : (14 : ℝ) ^ 6 < exp 16 := by
  have := exp_one_pow_gt 16 (by norm_num)
  norm_num at this ⊢
  linarith

lemma exp16_lt : exp 16 < 10 ^ 8 := by
  have := exp_one_pow_lt 16 (by norm_num)
  norm_num at this ⊢
  linarith

/-- `x^{1/3} ≤ √x / c` once `c⁶ ≤ x`. -/
lemma rpow_third_le {x c : ℝ} (hc : 0 < c) (hx : c ^ 6 ≤ x) :
    x ^ ((1 : ℝ) / 3) ≤ √x / c := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h6 : c ≤ x ^ ((1 : ℝ) / 6) := by
    have := rpow_le_rpow (by positivity) hx (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rwa [← rpow_natCast, ← rpow_mul hc.le, show ((6 : ℕ) : ℝ) * (1 / 6) = 1 by norm_num,
      rpow_one] at this
  have hs : √x = x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 6) := by
    rw [sqrt_eq_rpow, ← rpow_add hx0]; norm_num
  rw [le_div_iff₀ hc, hs]
  exact mul_le_mul_of_nonneg_left h6 (rpow_nonneg hx0.le _)

/-- Schoenfeld 1976 (6.13) in the form used: from (6.11) and [10, (3.39)],
`|θ(x) - x| < √x log x (log x - α₅)/(8π) + 1.02√x + 3x^{1/3}`. -/
theorem display_6_13 (hRH : RiemannHypothesis) (ξ x : ℝ) (hξ : 82800 ≤ ξ) (hx : ξ ≤ x) :
    |Chebyshev.theta x - x| <
      √x * log x * (log x - alpha5 ξ) / (8 * π) + (1.02 * √x + 3 * x ^ ((1 : ℝ) / 3)) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := sqrt_pos.mpr hx0
  have hpi : 0 < π := pi_pos
  have h611 := display_6_11 hRH ξ x hξ hx
  have hpsi : |Chebyshev.psi x - x| <
      √x * log x * (log x - alpha5 ξ) / (8 * π) := by
    rw [div_lt_iff₀ hx0] at h611
    have e : log x * (log x - alpha5 ξ) / (8 * π * √x) * x =
        √x * log x * (log x - alpha5 ξ) / (8 * π) := by
      have hxx : x = √x * √x := (mul_self_sqrt hx0.le).symm
      rw [show log x * (log x - alpha5 ξ) / (8 * π * √x) * x =
          log x * (log x - alpha5 ξ) / (8 * π) * (x / √x) by field_simp, div_sqrt]
      ring
    linarith
  have h339 := rs62_3_39 x hx0
  have hθψ := Chebyshev.theta_le_psi x
  have : |Chebyshev.theta x - x| ≤ |Chebyshev.psi x - x| +
      (Chebyshev.psi x - Chebyshev.theta x) := by
    rw [abs_le]; constructor <;> cases abs_cases (Chebyshev.psi x - x) <;> linarith
  linarith

/-- **Schoenfeld 1976 Theorem 10, display (6.1), θ half**, assembled from the leaves:
under RH, `|θ(x) - x| < √x (log x - 2) log x / (8π)` for `x ≥ 23·10⁸`.
CONDITIONAL ON the cited leaves of this file. -/
theorem thm10_61_S70 : RiemannHypothesis → ∀ x : ℝ, 23 * 10 ^ 8 ≤ x →
    |Chebyshev.theta x - x| < √x * (log x - 2) * log x / (8 * π) := by
  intro hRH x hx
  have h613 := display_6_13 hRH (23 * 10 ^ 8) x (by norm_num) hx
  have ha := alpha5_23e8
  have hL := log_ge_215 hx
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := sqrt_pos.mpr hx0
  have hpi : 0 < π := pi_pos
  have hpi4 : π < 3.1416 := pi_lt_d4
  have h3 := rpow_third_le (by norm_num : (0 : ℝ) < 36) (by linarith : (36 : ℝ) ^ 6 ≤ x)
  have _hk : 0 ≤ 1.292 * log x - (1.02 + 3 / 36) * (8 * π) := by nlinarith
  have hA : √x * log x * (log x - alpha5 (23 * 10 ^ 8)) ≤ √x * log x * (log x - 3.292) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have key : √x * log x * (log x - alpha5 (23 * 10 ^ 8)) / (8 * π) +
      (1.02 * √x + 3 * x ^ ((1 : ℝ) / 3)) ≤ √x * (log x - 2) * log x / (8 * π) := by
    rw [div_add' _ _ _ (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    have : 0 ≤ √x * (1.292 * log x - (1.02 + 3 / 36) * (8 * π)) := mul_nonneg hs.le _hk
    have h3' : 3 * x ^ ((1 : ℝ) / 3) * (8 * π) ≤ 3 * (√x / 36) * (8 * π) := by
      have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 3 * (8 * π)); linarith
    nlinarith
  linarith

/-- (6.3) for `x ≥ e¹⁶`: (6.13) with `ξ = e¹⁶`, where `α₅ > 2.02`. -/
theorem range_e16 (hRH : RiemannHypothesis) (x : ℝ) (hx : exp 16 ≤ x) :
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) := by
  have h14 := exp16_gt
  have h613 := display_6_13 hRH (exp 16) x (by norm_num at h14; linarith) hx
  have ha := alpha5_e16
  have hL : 16 ≤ log x := by rw [le_log_iff_exp_le (by linarith)]; exact hx
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := sqrt_pos.mpr hx0
  have hpi : 0 < π := pi_pos
  have hpi4 : π < 3.1416 := pi_lt_d4
  have h3 := rpow_third_le (by norm_num : (0 : ℝ) < 14) (by linarith : (14 : ℝ) ^ 6 ≤ x)
  have hk : 0 ≤ 2.02 * log x - (1.02 + 3 / 14) * (8 * π) := by nlinarith
  have hA : √x * log x * (log x - alpha5 (exp 16)) ≤ √x * log x * (log x - 2.02) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have key : √x * log x * (log x - alpha5 (exp 16)) / (8 * π) +
      (1.02 * √x + 3 * x ^ ((1 : ℝ) / 3)) ≤ √x * log x ^ 2 / (8 * π) := by
    rw [div_add' _ _ _ (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    have : 0 ≤ √x * (2.02 * log x - (1.02 + 3 / 14) * (8 * π)) := mul_nonneg hs.le hk
    have h3' : 3 * x ^ ((1 : ℝ) / 3) * (8 * π) ≤ 3 * (√x / 14) * (8 * π) := by
      have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 3 * (8 * π)); linarith
    nlinarith
  linarith

/-- (6.16) for `599 ≤ x < e¹⁶`: the lower bound from (6.15) with [10, Theorem 18] for
`x ≥ 1400`, [10, Theorem 19] for `1200 ≤ x < 1400`, and the Rosser-Walker tables below. -/
theorem display_6_16 (x : ℝ) (h1 : 599 ≤ x) (h2 : x < exp 16) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := sqrt_pos.mpr hx0
  have hpi : 0 < π := pi_pos
  have hpi4 : π < 3.1416 := pi_lt_d4
  have hx8 : x ≤ 10 ^ 8 := by linarith [exp16_lt]
  by_cases h1400 : 1400 ≤ x
  · have hL := log_ge_72 h1400
    have h18 := (rs62_thm18 x hx0 hx8).1
    have hk : 2.05282 * (8 * π) < log x ^ 2 := by nlinarith
    have : 2.05282 * √x < √x * log x ^ 2 / (8 * π) := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  by_cases h1200 : 1200 ≤ x
  · have hL := log_ge_709 h1200
    have h19 := rs62_thm19 x (Or.inl ⟨hx0, by linarith⟩)
    have hk : 2 * (8 * π) < log x ^ 2 := by nlinarith
    have : 2 * √x < √x * log x ^ 2 / (8 * π) := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  exact rosser_walker_599 x h1 (by linarith)

/-- **Schoenfeld 1976 Theorem 10, display (6.3)**, assembled from the leaves:
under RH, `|θ(x) - x| < √x log² x / (8π)` for `x ≥ 599`.
CONDITIONAL ON the cited leaves of this file. -/
theorem thm10_63_S70 : RiemannHypothesis → ∀ x : ℝ, 599 ≤ x →
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) := by
  intro hRH x hx
  by_cases h16 : exp 16 ≤ x
  · exact range_e16 hRH x h16
  rw [not_le] at h16
  have hx0 : 0 < x := by linarith
  have hpos : 0 < √x * log x ^ 2 / (8 * π) := by
    have : 0 < log x := log_pos (by linarith)
    have : 0 < √x := sqrt_pos.mpr hx0
    have := pi_pos
    positivity
  have hup := (rs62_thm18 x hx0 (by linarith [exp16_lt])).2
  have hlo := display_6_16 x hx h16
  rw [abs_lt]; constructor <;> linarith

end

end LeanLab.BS2022GRH.SchoenfeldThm10S70

#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.display_6_13
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.thm10_61_S70
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.range_e16
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.display_6_16
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.thm10_63_S70
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.log_ge_215
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.log_ge_72
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.log_ge_709
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.exp16_gt
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.exp16_lt
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.rpow_third_le
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.alpha5_e16
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.alpha5_23e8
#print axioms LeanLab.BS2022GRH.SchoenfeldThm10S70.loglogxi_bounds
