/-
Schoenfeld 1976, Math. Comp. 30, pp. 337-338: the split of display (6.11) along the
displays (6.6) to (6.10) of the proof of Theorem 10.

* The first display on p. 338 after "We now apply Lemmas 8 and 9 with m = 1": the
  output of Rosser-Schoenfeld 1975 Lemmas 8 and 9 under RH, a cited HARD leaf.
* (6.6): `δ ≤ α₂`, PROVED.
* The bound `log(T₁/2π) + 1 ≤ (log x - α₃)/2` on p. 338 with (6.8), PROVED.
* `α₄ > 0` after (6.10), PROVED.
* The second display on p. 338, display (6.9) and display (6.11), PROVED as algebra
  from the cited leaf.

AI wrote this Lean code, Claude, ROUTE BURST S76 burst-20261122, unit display_6_11_split.
Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.SchoenfeldThm10S70

namespace LeanLab.BS2022GRH.SchoenfeldD611S76
open Real LeanLab.BS2022GRH.SchoenfeldThm10S70

noncomputable section

/-- Schoenfeld 1976 display (6.6): `δ = log x/(π√x)`. -/
def delta (x : ℝ) : ℝ := log x / (π * √x)

/-- Schoenfeld 1976 display (6.7): `α₁ = log² ξ/(π√ξ)`. -/
def alpha1 (ξ : ℝ) : ℝ := log ξ ^ 2 / (π * √ξ)

/-- Schoenfeld 1976 display (6.7): `α₂ = log ξ/(π√ξ)`. -/
def alpha2 (ξ : ℝ) : ℝ := log ξ / (π * √ξ)

/-- Schoenfeld 1976 display (6.8): `δ₁ = α₂(1 + α₂)/(2 + α₂)`. -/
def delta1 (ξ : ℝ) : ℝ := alpha2 ξ * (1 + alpha2 ξ) / (2 + alpha2 ξ)

/-- Schoenfeld 1976 display (6.8): `α₃ = 2 log log ξ - 2(1 + δ₁)`. -/
def alpha3 (ξ : ℝ) : ℝ := 2 * log (log ξ) - 2 * (1 + delta1 ξ)

/-- Schoenfeld 1976 display (6.10): `α₄ = 2α₃ - (α₃² + 4.152828)/log ξ`. -/
def alpha4 (ξ : ℝ) : ℝ := 2 * alpha3 ξ - (alpha3 ξ ^ 2 + 4.152828) / log ξ

/-- Rosser-Schoenfeld 1975 display (4.2) at m = 1, in the form written in Schoenfeld
1976 p. 338 first display: `T₁/2π = (√x/log x)·(2 + 2δ + δ²)/(2 + δ)`. -/
def T1 (x : ℝ) : ℝ :=
  2 * π * (√x / log x * ((2 + 2 * delta x + delta x ^ 2) / (2 + delta x)))

/-- Schoenfeld 1976 display (6.12) in terms of the named constants. -/
lemma alpha5_eq (ξ : ℝ) :
    alpha5 ξ = alpha4 ξ - alpha1 ξ / 2 - 4 - 8 * π * log (2 * π) / (√ξ * log ξ) := rfl

/-- Rosser-Schoenfeld 1975 displays (3.6) and (4.2) at m = 1:
`T₁ = (1/δ)·2R₁(δ)/(2 + δ)` with `R₁(δ) = (1 + δ)² + 1`. -/
def T1rs (δ : ℝ) : ℝ := 1 / δ * (2 * ((1 + δ) ^ 2 + 1) / (2 + δ))

/-! ### The cited leaf -/

/-- LEAF: Rosser-Schoenfeld 1975 Lemma 8, display (3.11), combined with Lemma 9,
display (4.5), at m = 1, as applied in Schoenfeld 1976 p. 338 "We now apply Lemmas 8 and 9
with m = 1": under RH all zeros have `β = 1/2`, so `S₃(1, δ) = 0 = S₄(1, δ)` by (3.9)
and (3.10), and (3.11) with (4.5) give, for `x > 1`, `0 < δ < (x - 1)/x` and
`T₁ ≥ D = 158.84998` of (4.3),
`(1/x)|ψ(x) - {x - log(2π) - ½ log(1 - x⁻²)}|
  < ((2 + δ)/(4π))·{(log(T₁/2π) + 1)² + 0.038207 + 1 - 2.82/(2T₁)}/√x + δ/2`. HARD. -/
theorem rs75_lemma8_lemma9_m1 : RiemannHypothesis → ∀ x δ : ℝ, 1 < x → 0 < δ →
    δ < (x - 1) / x → 158.84998 ≤ T1rs δ →
    1 / x * |Chebyshev.psi x - (x - log (2 * π) - 1 / 2 * log (1 - 1 / x ^ 2))| <
      (2 + δ) / (4 * π) *
          ((log (T1rs δ / (2 * π)) + 1) ^ 2 + 0.038207 + 1 - 2.82 / (2 * T1rs δ)) / √x +
        δ / 2 := by
  sorry

/-! ### Proved steps -/

/-- `log y ≤ y/2` for `y > 0`. -/
lemma log_le_half {y : ℝ} (hy : 0 < y) : log y ≤ y / 2 := by
  have h1 := Real.log_le_sub_one_of_pos (sqrt_pos.2 hy)
  have h2 : log √y = log y / 2 := Real.log_sqrt hy.le
  have h3 := sq_sqrt hy.le
  nlinarith [sq_nonneg (√y - 2)]

/-- `11 ≤ log ξ` for `ξ ≥ 82800`. -/
lemma log_ge_11 {ξ : ℝ} (hξ : 82800 ≤ ξ) : 11 ≤ log ξ := by
  rw [le_log_iff_exp_le (by linarith)]
  have h1 := exp_one_pow_lt 11 (by norm_num)
  have h2 : (2.7182818286 : ℝ) ^ 11 < 82800 := by norm_num
  push_cast at h1
  linarith

/-- `2 ≤ log y` for `y ≥ 11`. -/
lemma two_le_log {y : ℝ} (hy : 11 ≤ y) : 2 ≤ log y := by
  rw [le_log_iff_exp_le (by linarith)]
  have h1 := exp_one_pow_lt 2 (by norm_num)
  have h2 : (2.7182818286 : ℝ) ^ 2 < 11 := by norm_num
  push_cast at h1
  linarith

/-- Schoenfeld 1976 display (6.6), the part used: `δ ≤ α₂` for `x ≥ ξ ≥ 82800`. -/
theorem display_6_6 {ξ x : ℝ} (hξ : 82800 ≤ ξ) (hx : ξ ≤ x) : delta x ≤ alpha2 ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hx0 : 0 < x := by linarith
  set a := √ξ with ha
  set b := √x with hb
  have ha0 : 0 < a := sqrt_pos.2 hξ0
  have hab : a ≤ b := sqrt_le_sqrt hx
  have hla : log x = 2 * log b := by rw [hb, Real.log_sqrt hx0.le]; ring
  have hlξ : log ξ = 2 * log a := by rw [ha, Real.log_sqrt hξ0.le]; ring
  have hLa : 1 ≤ log a := by have := log_ge_11 hξ; linarith
  have hba : log b ≤ log a + (b / a - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le ha0 hab) ha0)
    rw [Real.log_div (by linarith) ha0.ne'] at h
    linarith
  have hkey : a * log b ≤ b * log a := by
    have : a * (b / a - 1) = b - a := by field_simp
    nlinarith
  unfold delta alpha2
  rw [hla, hlξ, div_le_div_iff₀ (by positivity) (by positivity)]
  have hpi := pi_pos
  nlinarith [mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 2 * π)]

lemma alpha2_nonneg {ξ : ℝ} (hξ : 82800 ≤ ξ) : 0 ≤ alpha2 ξ := by
  have := log_ge_11 hξ
  unfold alpha2
  have := pi_pos
  positivity

lemma delta1_nonneg {ξ : ℝ} (hξ : 82800 ≤ ξ) : 0 ≤ delta1 ξ := by
  have := alpha2_nonneg hξ
  unfold delta1
  positivity

/-- Schoenfeld 1976 p. 338: `log(T₁/2π) + 1 ≤ ½(log x - α₃)`, with (6.6) and (6.8);
also the left side is nonnegative. -/
theorem T1_bound {ξ x : ℝ} (hξ : 82800 ≤ ξ) (hx : ξ ≤ x) :
    0 ≤ log (T1 x / (2 * π)) + 1 ∧
      log (T1 x / (2 * π)) + 1 ≤ (log x - alpha3 ξ) / 2 := by
  have hξ0 : 0 < ξ := by linarith
  have hx0 : 0 < x := by linarith
  have hLξ := log_ge_11 hξ
  have hL : 11 ≤ log x := log_ge_11 (le_trans hξ hx)
  have hLL : log ξ ≤ log x := log_le_log hξ0 hx
  have hpi := pi_pos
  have hd0 : 0 ≤ delta x := by unfold delta; positivity
  have hd := display_6_6 hξ hx
  have ha2 := alpha2_nonneg hξ
  have hT : T1 x / (2 * π) = √x / log x *
      ((2 + 2 * delta x + delta x ^ 2) / (2 + delta x)) := by
    unfold T1; field_simp
  set d := delta x
  set q := (2 + 2 * d + d ^ 2) / (2 + d) with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ (by positivity)]; nlinarith
  have hqd : q - 1 ≤ delta1 ξ := by
    unfold delta1
    have : q - 1 = d * (1 + d) / (2 + d) := by rw [hq]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hd0 ha2, mul_nonneg (sub_nonneg.2 hd) (mul_nonneg hd0 ha2)]
  have hs0 : 0 < √x := sqrt_pos.2 hx0
  have hlog : log (T1 x / (2 * π)) = log x / 2 - log (log x) + log q := by
    rw [hT, Real.log_mul (by positivity) (by positivity), Real.log_div hs0.ne' (by positivity),
      Real.log_sqrt hx0.le]
  have hlq0 : 0 ≤ log q := Real.log_nonneg hq1
  have hlq : log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hll : log (log ξ) ≤ log (log x) := log_le_log (by linarith) hLL
  have hlh := log_le_half (show 0 < log x by linarith)
  constructor
  · rw [hlog]; linarith
  · rw [hlog]; unfold alpha3; linarith

/-- Schoenfeld 1976 after (6.10): `α₄ > 0` for `ξ ≥ 82800`. -/
theorem alpha4_pos {ξ : ℝ} (hξ : 82800 ≤ ξ) : 0 < alpha4 ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hLξ := log_ge_11 hξ
  have hll := two_le_log hLξ
  have hlh := log_le_half (show 0 < log ξ by linarith)
  have hll2 := log_le_half (show 0 < log (log ξ) by linarith)
  have hpi := pi_gt_three
  have hd1 := delta1_nonneg hξ
  have ha2 := alpha2_nonneg hξ
  have hs : 0 < √ξ := sqrt_pos.2 hξ0
  -- `log ξ ≤ 2 √ξ`, so `α₂ ≤ 2/π < 0.7`
  have hlogs : log ξ ≤ 2 * √ξ := by
    have h1 := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hξ0.le] at h1
    linarith
  have ha2u : alpha2 ξ ≤ 0.7 := by
    unfold alpha2; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hd1u : delta1 ξ ≤ 0.7 := by
    unfold delta1; rw [div_le_iff₀ (by positivity)]; nlinarith
  have h3l : 0.6 ≤ alpha3 ξ := by unfold alpha3; linarith
  have h3u : alpha3 ξ ≤ log ξ - 2 := by unfold alpha3; linarith
  unfold alpha4
  have : (alpha3 ξ ^ 2 + 4.152828) / log ξ < 2 * alpha3 ξ := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h3u (by linarith : (0 : ℝ) ≤ alpha3 ξ)]
  linarith

/-- Schoenfeld 1976 display (6.6), first inequality: `log² x/√x ≤ log² ξ/√ξ` for
`x ≥ ξ ≥ 82800`, hence `δ ≤ α₁/log x`. -/
theorem display_6_6_sq {ξ x : ℝ} (hξ : 82800 ≤ ξ) (hx : ξ ≤ x) :
    log x ^ 2 / √x ≤ log ξ ^ 2 / √ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hx0 : 0 < x := by linarith
  set a := √ξ with ha
  set b := √x with hb
  have ha0 : 0 < a := sqrt_pos.2 hξ0
  have hb0 : 0 < b := sqrt_pos.2 hx0
  have hab : a ≤ b := sqrt_le_sqrt hx
  have hla : log x = 2 * log b := by rw [hb, Real.log_sqrt hx0.le]; ring
  have hlξ : log ξ = 2 * log a := by rw [ha, Real.log_sqrt hξ0.le]; ring
  have hu : 2 ≤ log a := by have := log_ge_11 hξ; linarith
  set u := log a
  set t := log b - log a with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith [log_le_log ha0 hab]
  have hbt : b = a * exp t := by
    rw [ht, exp_sub, exp_log hb0, exp_log ha0]; field_simp
  have hq := quadratic_le_exp_of_nonneg ht0
  have hkey : a * (log b) ^ 2 ≤ b * u ^ 2 := by
    have hlb : log b = u + t := by rw [ht]; ring
    rw [hlb, hbt]
    have h1 : (u + t) ^ 2 ≤ (1 + t + t ^ 2 / 2) * u ^ 2 := by
      nlinarith [mul_nonneg ht0 (mul_nonneg (by linarith : (0:ℝ) ≤ u) (by linarith : (0:ℝ) ≤ u - 2)),
        mul_nonneg (sq_nonneg t) (by nlinarith : (0:ℝ) ≤ u ^ 2 / 2 - 1)]
    have h2 : (1 + t + t ^ 2 / 2) * u ^ 2 ≤ exp t * u ^ 2 :=
      mul_le_mul_of_nonneg_right hq (sq_nonneg u)
    nlinarith
  rw [hla, hlξ, div_le_div_iff₀ hb0 ha0]
  nlinarith

/-- `log 82800 ≤ 11.33`. -/
lemma log_82800_le : log (82800 : ℝ) ≤ 11.33 := by
  rw [log_le_iff_le_exp (by norm_num), show (11.33 : ℝ) = (11 : ℕ) + 0.33 by norm_num,
    exp_add, ← exp_one_pow]
  have h1 := exp_one_gt_d9
  have h2 := exp_lower 0.33 (by norm_num) (by norm_num)
  have h3 : (2.7182818283 : ℝ) ^ 11 ≤ exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) h1.le 11
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have h4 := mul_le_mul h3 h2 (by norm_num) (by positivity)
  norm_num at h4 ⊢
  linarith

/-- Schoenfeld 1976 (6.7): `δ ≤ α₂(82800) < 0.01255`, so `T₁ > D` at m = 1. -/
lemma delta_le_small {x : ℝ} (hx : 82800 ≤ x) : delta x ≤ 0.01255 := by
  have h := display_6_6 (le_refl (82800 : ℝ)) hx
  have hl := log_82800_le
  have hs : (287.7 : ℝ) ≤ √82800 := by
    rw [show (287.7 : ℝ) = √(287.7 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hpi := pi_gt_d6
  have : alpha2 82800 ≤ 0.01255 := by
    unfold alpha2
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hpi.le hs (by norm_num) pi_pos.le]
  linarith

/-- Schoenfeld 1976 p. 338, the first display after "We now apply Lemmas 8 and 9 with
m = 1 to get": PROVED from the cited leaf `rs75_lemma8_lemma9_m1` with `δ` of (6.6),
`T₁ > D` and (6.6). Under RH, for `x ≥ ξ ≥ 82800`,
`|ψ(x) - x|/x < (1 + α₁/(2 log x))((log(T₁/2π) + 1)² + 1.038207)/(2π√x)
  + log x/(2π√x) + (log(2π) + ½ log(1 - 1/x²))/x`. -/
theorem rs75_lemmas_8_9 : RiemannHypothesis → ∀ ξ x : ℝ, 82800 ≤ ξ → ξ ≤ x →
    |Chebyshev.psi x - x| / x <
      1 / (2 * π * √x) * (1 + alpha1 ξ / (2 * log x)) *
          ((log (T1 x / (2 * π)) + 1) ^ 2 + 1.038207) +
        log x / (2 * π * √x) + 1 / x * (log (2 * π) + 1 / 2 * log (1 - 1 / x ^ 2)) := by
  intro hRH ξ x hξ hx
  have hξ0 : 0 < ξ := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hL : 11 ≤ log x := log_ge_11 (le_trans hξ hx)
  have hpi := pi_pos
  have hs0 : 0 < √x := sqrt_pos.2 hx0
  set L := log x with hLdef
  set δ := delta x with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; unfold delta; positivity
  have hδu : δ ≤ 0.01255 := delta_le_small (le_trans hξ hx)
  have hδx : δ < (x - 1) / x := by
    rw [lt_div_iff₀ hx0]; nlinarith
  have hTeq : T1 x = T1rs δ := by
    unfold T1 T1rs
    rw [hδdef]; unfold delta
    field_simp
    ring
  have hprod : T1rs δ * δ = 2 * ((1 + δ) ^ 2 + 1) / (2 + δ) := by
    unfold T1rs; field_simp
  have h2le : 2 ≤ 2 * ((1 + δ) ^ 2 + 1) / (2 + δ) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hT0 : 0 < T1rs δ := by unfold T1rs; positivity
  have hTD : 158.84998 ≤ T1rs δ := by nlinarith
  have h := rs75_lemma8_lemma9_m1 hRH x δ hx1 hδ0 hδx hTD
  rw [← hTeq] at h
  -- the constant term `c = log(2π) + ½ log(1 - 1/x²)` is nonnegative
  set c := log (2 * π) + 1 / 2 * log (1 - 1 / x ^ 2) with hc
  have hx2 : 1 / x ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hy0 : 0 < 1 - 1 / x ^ 2 := by linarith
  have hlogy := Real.one_sub_inv_le_log_of_pos hy0
  have hinv : (1 - 1 / x ^ 2)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hy0 (by norm_num)]; linarith
  have hl2pi : 1 ≤ log (2 * π) := by
    rw [le_log_iff_exp_le (by positivity)]
    have := exp_one_lt_d9
    linarith [pi_gt_three]
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have htri : |Chebyshev.psi x - x| / x ≤
      1 / x * |Chebyshev.psi x - (x - log (2 * π) - 1 / 2 * log (1 - 1 / x ^ 2))| +
        1 / x * c := by
    rw [← mul_add, one_div_mul_eq_div]
    apply div_le_div_of_nonneg_right _ hx0.le
    have : Chebyshev.psi x - x =
        (Chebyshev.psi x - (x - log (2 * π) - 1 / 2 * log (1 - 1 / x ^ 2))) - c := by
      rw [hc]; ring
    rw [this]
    calc _ ≤ |Chebyshev.psi x - (x - log (2 * π) - 1 / 2 * log (1 - 1 / x ^ 2))| + |c| :=
          abs_sub _ _
      _ = _ := by rw [abs_of_nonneg hc0]
  -- (6.6): `δ ≤ α₁/log x`
  have hsq := display_6_6_sq hξ hx
  have hδa1 : δ / 2 ≤ alpha1 ξ / (2 * L) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : δ * L = L ^ 2 / √x / π := by rw [hδdef, hLdef]; unfold delta; field_simp
    have h2 : L ^ 2 / √x / π ≤ alpha1 ξ := by
      have e : alpha1 ξ = log ξ ^ 2 / √ξ / π := by unfold alpha1; field_simp
      rw [e]
      exact div_le_div_of_nonneg_right hsq pi_pos.le
    nlinarith
  set A := (log (T1 x / (2 * π)) + 1) ^ 2 with hA
  have hA0 : 0 ≤ A := sq_nonneg _
  have hTx0 : 0 < T1 x := by rw [hTeq]; exact hT0
  have hdrop : (2 + δ) / (4 * π) * (A + 0.038207 + 1 - 2.82 / (2 * T1 x)) / √x ≤
      1 / (2 * π * √x) * (1 + alpha1 ξ / (2 * L)) * (A + 1.038207) := by
    have h282 : 0 ≤ 2.82 / (2 * T1 x) := by positivity
    have e : (2 + δ) / (4 * π) * (A + 1.038207) / √x =
        1 / (2 * π * √x) * (1 + δ / 2) * (A + 1.038207) := by field_simp; ring
    have m1 : (2 + δ) / (4 * π) * (A + 0.038207 + 1 - 2.82 / (2 * T1 x)) / √x ≤
        (2 + δ) / (4 * π) * (A + 1.038207) / √x := by
      apply div_le_div_of_nonneg_right _ hs0.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have m2 : 1 / (2 * π * √x) * (1 + δ / 2) * (A + 1.038207) ≤
        1 / (2 * π * √x) * (1 + alpha1 ξ / (2 * L)) * (A + 1.038207) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have hδ2 : δ / 2 = L / (2 * π * √x) := by rw [hδdef]; unfold delta; field_simp; ring
  linarith

/-- Schoenfeld 1976 p. 338, the second display after "We now apply Lemmas 8 and 9":
`|ψ(x) - x|/x < (1 + α₁/(2 log x))(log² x - 2α₃ log x + α₃² + 4.152828)/(8π√x)
  + log x/(2π√x) + log(2π)/x`. -/
theorem display_p338_second (hRH : RiemannHypothesis) {ξ x : ℝ} (hξ : 82800 ≤ ξ)
    (hx : ξ ≤ x) :
    |Chebyshev.psi x - x| / x <
      1 / (8 * π * √x) * (1 + alpha1 ξ / (2 * log x)) *
          (log x ^ 2 - 2 * alpha3 ξ * log x + alpha3 ξ ^ 2 + 4.152828) +
        log x / (2 * π * √x) + log (2 * π) / x := by
  have h := rs75_lemmas_8_9 hRH ξ x hξ hx
  obtain ⟨hT0, hT1⟩ := T1_bound hξ hx
  have hξ0 : 0 < ξ := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hL : 11 ≤ log x := log_ge_11 (le_trans hξ hx)
  have hpi := pi_pos
  have hs0 : 0 < √x := sqrt_pos.2 hx0
  have ha1 : 0 ≤ alpha1 ξ := by unfold alpha1; positivity
  have hK : 0 ≤ 1 / (2 * π * √x) * (1 + alpha1 ξ / (2 * log x)) := by
    have : 0 ≤ alpha1 ξ / (2 * log x) := by positivity
    positivity
  have hsq : (log (T1 x / (2 * π)) + 1) ^ 2 ≤ ((log x - alpha3 ξ) / 2) ^ 2 :=
    pow_le_pow_left₀ hT0 hT1 2
  have h1 := mul_le_mul_of_nonneg_left (add_le_add_right hsq 1.038207) hK
  have hlog1 : log (1 - 1 / x ^ 2) ≤ 0 := by
    apply Real.log_nonpos
    · rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    · have : 0 ≤ 1 / x ^ 2 := by positivity
      linarith
  have h2 : 1 / x * (log (2 * π) + 1 / 2 * log (1 - 1 / x ^ 2)) ≤ log (2 * π) / x := by
    rw [one_div_mul_eq_div]
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith
  have heq : 1 / (2 * π * √x) * (1 + alpha1 ξ / (2 * log x)) *
      (((log x - alpha3 ξ) / 2) ^ 2 + 1.038207) =
      1 / (8 * π * √x) * (1 + alpha1 ξ / (2 * log x)) *
        (log x ^ 2 - 2 * alpha3 ξ * log x + alpha3 ξ ^ 2 + 4.152828) := by
    field_simp; ring
  linarith

/-- Schoenfeld 1976 display (6.9):
`|ψ(x) - x|/x < (1 + α₁/(2 log x))(log² x - α₄ log x)/(8π√x)
  + (log x/(8π√x))(4 + 8π log(2π)/(√x log x))`. -/
theorem display_6_9 (hRH : RiemannHypothesis) {ξ x : ℝ} (hξ : 82800 ≤ ξ) (hx : ξ ≤ x) :
    |Chebyshev.psi x - x| / x <
      1 / (8 * π * √x) * (1 + alpha1 ξ / (2 * log x)) * (log x ^ 2 - alpha4 ξ * log x) +
        log x / (8 * π * √x) * (4 + 8 * π * log (2 * π) / (√x * log x)) := by
  have h := display_p338_second hRH hξ hx
  have hξ0 : 0 < ξ := by linarith
  have hx0 : 0 < x := by linarith
  have hLξ := log_ge_11 hξ
  have hL : 11 ≤ log x := log_ge_11 (le_trans hξ hx)
  have hLL : log ξ ≤ log x := log_le_log hξ0 hx
  have hpi := pi_pos
  have hs0 : 0 < √x := sqrt_pos.2 hx0
  have ha1 : 0 ≤ alpha1 ξ := by unfold alpha1; positivity
  have hK : 0 ≤ 1 / (8 * π * √x) * (1 + alpha1 ξ / (2 * log x)) := by
    have : 0 ≤ alpha1 ξ / (2 * log x) := by positivity
    positivity
  have hpoly : log x ^ 2 - 2 * alpha3 ξ * log x + alpha3 ξ ^ 2 + 4.152828 ≤
      log x ^ 2 - alpha4 ξ * log x := by
    unfold alpha4
    have hc : 0 ≤ alpha3 ξ ^ 2 + 4.152828 := by positivity
    have : (alpha3 ξ ^ 2 + 4.152828) ≤ (alpha3 ξ ^ 2 + 4.152828) / log ξ * log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left hLL hc
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hpoly hK
  have hxs : x = √x * √x := (mul_self_sqrt hx0.le).symm
  have heq : log x / (8 * π * √x) * (4 + 8 * π * log (2 * π) / (√x * log x)) =
      log x / (2 * π * √x) + log (2 * π) / x := by
    have e2 : log (2 * π) / x = log (2 * π) / (√x * √x) := by rw [← hxs]
    rw [e2]; field_simp; ring
  linarith

/-- Schoenfeld 1976, the algebra from (6.9) to (6.11) with (6.12), in generic form. -/
lemma step_6_11 (L s α1 α4 Lξ sξ lg : ℝ) (hL : 0 < L) (hs : 0 < s) (hα1 : 0 ≤ α1)
    (hα4 : 0 ≤ α4) (hlg : 0 ≤ lg) (hξ0 : 0 < sξ * Lξ) (hmono : sξ * Lξ ≤ s * L) :
    1 / (8 * π * s) * (1 + α1 / (2 * L)) * (L ^ 2 - α4 * L) +
        L / (8 * π * s) * (4 + 8 * π * lg / (s * L)) ≤
      L * (L - (α4 - α1 / 2 - 4 - 8 * π * lg / (sξ * Lξ))) / (8 * π * s) := by
  have hpi := pi_pos
  have hAB : 8 * π * lg / (s * L) ≤ 8 * π * lg / (sξ * Lξ) :=
    div_le_div_of_nonneg_left (by positivity) hξ0 hmono
  have e1 : 1 / (8 * π * s) * (1 + α1 / (2 * L)) * (L ^ 2 - α4 * L) +
      L / (8 * π * s) * (4 + 8 * π * lg / (s * L)) =
      ((L + α1 / 2) * (L - α4) + 4 * L + L * (8 * π * lg / (s * L))) / (8 * π * s) := by
    field_simp; ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_nonneg hα1 hα4, mul_le_mul_of_nonneg_left hAB hL.le]

/-- **Schoenfeld 1976 display (6.11)**, assembled: under RH, for `x ≥ ξ ≥ 82800`,
`|ψ(x) - x|/x < (log x)(log x - α₅)/(8π√x)`.
CONDITIONAL ON the cited leaf `rs75_lemmas_8_9`. -/
theorem display_6_11_S76 : RiemannHypothesis → ∀ ξ x : ℝ, 82800 ≤ ξ → ξ ≤ x →
    |Chebyshev.psi x - x| / x < log x * (log x - alpha5 ξ) / (8 * π * √x) := by
  intro hRH ξ x hξ hx
  have h := display_6_9 hRH hξ hx
  have hξ0 : 0 < ξ := by linarith
  have hx0 : 0 < x := by linarith
  have hLξ := log_ge_11 hξ
  have hL : 11 ≤ log x := log_ge_11 (le_trans hξ hx)
  have hLL : log ξ ≤ log x := log_le_log hξ0 hx
  have hpi := pi_pos
  have hs0 : 0 < √x := sqrt_pos.2 hx0
  have hsξ : 0 < √ξ := sqrt_pos.2 hξ0
  have hss : √ξ ≤ √x := sqrt_le_sqrt hx
  have ha1 : 0 ≤ alpha1 ξ := by unfold alpha1; positivity
  have hlg : 0 ≤ log (2 * π) := Real.log_nonneg (by linarith [pi_gt_three])
  have hst := step_6_11 (log x) (√x) (alpha1 ξ) (alpha4 ξ) (log ξ) (√ξ) (log (2 * π))
    (by linarith) hs0 ha1 (alpha4_pos hξ).le hlg (by positivity)
    (mul_le_mul hss hLL (by linarith) hs0.le)
  rw [alpha5_eq]
  linarith

end

end LeanLab.BS2022GRH.SchoenfeldD611S76

#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.display_6_11_S76
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.display_6_9
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.display_p338_second
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.display_6_6
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.display_6_6_sq
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.rs75_lemmas_8_9
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.delta_le_small
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.T1_bound
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.alpha4_pos
#print axioms LeanLab.BS2022GRH.SchoenfeldD611S76.step_6_11
