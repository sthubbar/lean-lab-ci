/-
Schoenfeld 1976, Math. Comp. 30, pp. 337-360, Corollary 1, display (6.18):
under RH, `|π x - li x| < √x log x / (8π)` for `x ≥ 2657`.

This file splits Schoenfeld's proof of (6.18) on pp. 339-340 into its own steps.
Each cited step is a `LEAF` with a class tag; the glue between them is proved.

* (6.1), θ half, and (6.3) of Theorem 10, the RH bounds for θ: split by S70 into the
  leaves of `SchoenfeldThm10S70`, see that file.
* (6.19a), which is [10, (4.17)], the partial summation identity for π via θ: MEDIUM leaf.
* [10, (7.6)], the partial integration identity for li: PROVED here from `liPV_eq`.
* (6.19b) with ξ = 10⁸, `ξ' ≅ 88.26`: MEDIUM numerical leaf, stated as `|ξ'| < 89`.
* The Brent range `5·10⁷ ≤ x ≤ 49·10⁸`, bound 4613.5: HARD numerical leaf.
* The Appel-Rosser table (6.20) on `[3169, 5·10⁷]` and its 2.444 variant on
  `[2659, 3169)`: MEDIUM numerical leaves.
* The direct calculation on `[2657, 2659)`: MEDIUM numerical leaf.

Proved glue: the combination of (6.19a) and [10, (7.6)] into the display after (6.19b),
the integral estimate of that display with `ξ = 10⁸`, the passage from each numerical
range to (6.18), and the assembly `cor1_6_18` of the statement `PaperInputs148.Lemma1J`.

Schoenfeld's `π` is the prime count up to and including `x`, which is `primeCount`;
his `li` is the principal value integral of [10], which is `liPV`. Schoenfeld's
inequality is strict; `Lemma1J` asks for `≤`, which is weaker.

AI wrote this Lean code, Claude, ROUTE BURST S63 burst-20261122, unit lemma1_schoenfeld.
Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.LiPV
import LeanLab.BS2022GRH.BrentRangeS63
import LeanLab.BS2022GRH.SchoenfeldXiS70
import LeanLab.BS2022GRH.SchoenfeldFiniteS70
import LeanLab.BS2022GRH.SchoenfeldThm10S70
import LeanLab.BS2022GRH.SchoenfeldWireS76

namespace LeanLab.BS2022GRH.SchoenfeldCor1S63
open Real MeasureTheory intervalIntegral Set
open LeanLab.BS2022GRH.PaperInputs148

noncomputable section

/-! ### Cited leaves -/

/-- Schoenfeld 1976 Theorem 10, display (6.1), the θ half. Was a HARD leaf; S70 split it
into the cited leaves of `SchoenfeldThm10S70`, glue proved there.
Under RH, `|θ x - x| < (1/(8π)) √x (log x - 2) log x` for `x ≥ 23·10⁸`.
Its proof is the RH explicit formula with Lemmas 8 and 9 of Rosser-Schoenfeld,
displays (6.6) to (6.14). -/
theorem thm10_61 : RiemannHypothesis → ∀ x : ℝ, 23 * 10 ^ 8 ≤ x →
    |Chebyshev.theta x - x| < √x * (log x - 2) * log x / (8 * π) :=
  SchoenfeldThm10S70.thm10_61_S70

/-- Schoenfeld 1976 Theorem 10, display (6.3). Was a HARD leaf; S70 split it
into the cited leaves of `SchoenfeldThm10S70`, glue proved there.
Under RH, `|θ x - x| < (1/(8π)) √x log² x` for `x ≥ 599`. Its proof is the RH explicit
formula for `x ≥ e¹⁶`, displays (6.6) to (6.14), and [10, Theorems 18, 19] with the
Rosser-Walker tables for `599 ≤ x < e¹⁶`, displays (6.15) and (6.16). -/
theorem thm10_63 : RiemannHypothesis → ∀ x : ℝ, 599 ≤ x →
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) :=
  SchoenfeldWireS76.thm10_63_S76

/-- `primeCount x` is Mathlib's `π ⌊x⌋₊`. -/
lemma primeCount_eq (x : ℝ) : primeCount x = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  unfold primeCount
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- The kernel `θ t / (t log² t)` is interval integrable on any interval in `(1, ∞)`. -/
lemma kern_ii {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => Chebyshev.theta t / (t * log t ^ 2)) volume a b := by
  have h1 : IntervalIntegrable Chebyshev.theta volume a b :=
    Chebyshev.theta_mono.intervalIntegrable
  have hpos : ∀ t ∈ uIcc a b, 1 < t := by
    intro t ht
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at ht; linarith [ht.1]
    · rw [uIcc_of_ge h] at ht; linarith [ht.1]
  have h2 : ContinuousOn (fun t : ℝ => (t * log t ^ 2)⁻¹) (uIcc a b) := by
    refine ContinuousOn.inv₀ (continuousOn_id.mul ((continuousOn_log.mono ?_).pow 2)) ?_
    · intro t ht; have := hpos t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith
    · intro t ht
      have := hpos t ht
      exact mul_ne_zero (by linarith) (pow_ne_zero 2 (log_pos this).ne')
  simpa [div_eq_mul_inv] using h1.mul_continuousOn h2

/-- Mathlib's Abel summation for `π` via `θ`, extended from `x ≥ 2` to `x > 1`. -/
lemma pc_formula {x : ℝ} (hx : 1 < x) :
    primeCount x = Chebyshev.theta x / log x
      + ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2) := by
  rcases le_or_gt 2 x with h2 | h2
  · rw [primeCount_eq]; exact Chebyshev.primeCounting_eq_theta_div_log_add_integral h2
  · have hfl : ⌊x⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]; constructor <;> push_cast <;> linarith
    have hpc : primeCount x = 0 := by
      rw [primeCount_eq, hfl]; simp
    have hth : Chebyshev.theta x = 0 := Chebyshev.theta_eq_zero_of_lt_two h2
    have hI : (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) = 0 := by
      rw [integral_symm, integral_of_le h2.le, integral_Ioc_eq_integral_Ioo,
        setIntegral_eq_zero_of_forall_eq_zero]
      · simp
      · intro t ht
        rw [Chebyshev.theta_eq_zero_of_lt_two ht.2, zero_div]
    rw [hpc, hth, hI]; simp

/-- LEAF: Schoenfeld 1976 display (6.19a), cited as Rosser-Schoenfeld 1962 (4.17). MEDIUM.
Partial summation: for `x ≥ ξ > 1`,
`π x - π ξ = θ x / log x - θ ξ / log ξ + ∫_ξ^x θ y / (y log² y) dy`. -/
theorem display_6_19a : ∀ ξ x : ℝ, 1 < ξ → ξ ≤ x →
    primeCount x - primeCount ξ = Chebyshev.theta x / log x - Chebyshev.theta ξ / log ξ
      + ∫ y in ξ..x, Chebyshev.theta y / (y * log y ^ 2) := by
  intro ξ x hξ hx
  have hx1 : 1 < x := lt_of_lt_of_le hξ hx
  rw [pc_formula hx1, pc_formula hξ, ← integral_interval_sub_left
    (kern_ii (a := 2) (by norm_num) hx1) (kern_ii (a := 2) (by norm_num) hξ)]
  ring

/-- `li x - li ξ = ∫_ξ^x dt / log t` for `x ≥ ξ > 1`, from `liPV_eq`. -/
lemma liPV_sub_eq (ξ x : ℝ) (hξ : 1 < ξ) (hx : ξ ≤ x) :
    liPV x - liPV ξ = ∫ t in ξ..x, 1 / log t := by
  have hn : (1 : ℝ) ∉ uIcc ξ x := by
    intro h; rw [uIcc_of_le hx] at h; linarith [h.1]
  rw [liPV_eq (lt_of_lt_of_le hξ hx), liPV_eq hξ]
  have hf : (fun t : ℝ => 1 / log t) = fun t => gli t + 1 / (t - 1) := funext inv_log_eq
  have hs : (∫ t in (0 : ℝ)..x, gli t) - (∫ t in (0 : ℝ)..ξ, gli t) = ∫ t in ξ..x, gli t :=
    integral_interval_sub_left (gli_ii (le_refl 0) (by linarith))
      (gli_ii (le_refl 0) (by linarith))
  rw [hf, integral_add (gli_ii (by linarith) (by linarith)) (inv_sub_one_ii hn),
    integral_inv_sub_one hn, log_div (by linarith) (by linarith)]
  linarith

/-- Integration by parts, `∫_ξ^x dt / log t = x/log x - ξ/log ξ + ∫_ξ^x dt / log² t`. -/
lemma parts (ξ x : ℝ) (hξ : 1 < ξ) (hx : ξ ≤ x) :
    (∫ t in ξ..x, 1 / log t) = x / log x - ξ / log ξ + ∫ y in ξ..x, 1 / log y ^ 2 := by
  have hsub : ∀ t ∈ uIcc ξ x, 1 < t := by
    intro t ht; rw [uIcc_of_le hx] at ht; linarith [ht.1]
  have key : ∀ t ∈ uIcc ξ x,
      HasDerivAt (fun t => t / log t) (1 / log t - 1 / log t ^ 2) t := by
    intro t ht
    have h1 := hsub t ht
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (log_pos h1).ne'
    have h := (hasDerivAt_id' t).div (hasDerivAt_log ht0) hl
    convert h using 1
    field_simp
  have hc1 : ContinuousOn (fun t : ℝ => 1 / log t) (uIcc ξ x) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_log.mono ?_) ?_
    · intro t ht; have := hsub t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith
    · intro t ht; exact (log_pos (hsub t ht)).ne'
  have hc2 : ContinuousOn (fun t : ℝ => 1 / log t ^ 2) (uIcc ξ x) := by
    refine ContinuousOn.div continuousOn_const ((continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; have := hsub t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith
    · intro t ht; exact pow_ne_zero 2 (log_pos (hsub t ht)).ne'
  have hI := integral_eq_sub_of_hasDerivAt key ((hc1.sub hc2).intervalIntegrable)
  rw [integral_sub hc1.intervalIntegrable hc2.intervalIntegrable] at hI
  linarith

/-- Rosser-Schoenfeld 1962 (7.6), used by Schoenfeld 1976 right after (6.19b). PROVED here
from the lab's `liPV_eq`. Partial integration of the logarithmic integral: for `x ≥ ξ > 1`,
`li x - li ξ = x / log x - ξ / log ξ + ∫_ξ^x dy / log² y`. -/
theorem rs62_7_6 : ∀ ξ x : ℝ, 1 < ξ → ξ ≤ x →
    liPV x - liPV ξ = x / log x - ξ / log ξ + ∫ y in ξ..x, 1 / log y ^ 2 := by
  intro ξ x hξ hx
  rw [liPV_sub_eq ξ x hξ hx, parts ξ x hξ hx]

/-- The quantity `ξ'` of Schoenfeld 1976 display (6.19b),
`ξ' = {li ξ - π ξ} - {ξ - θ ξ} / log ξ`. -/
def xiPrime (ξ : ℝ) : ℝ :=
  (liPV ξ - primeCount ξ) - (ξ - Chebyshev.theta ξ) / log ξ

/-- Schoenfeld 1976 p. 340 line 1, "Taking ξ = 10⁸, we obtain ξ' ≅ 88.26", stated with the
rounded margin `|ξ'| < 89`, which is all the proof uses. Was a LEAF; S70 split it into the
three values `π 10⁸`, `θ 10⁸`, `li 10⁸`, LEAFs in SchoenfeldXiS70, with the rest proved there. -/
theorem xiPrime_1e8 : |xiPrime (10 ^ 8)| < 89 := by
  unfold xiPrime
  exact SchoenfeldXiS70.xiPrime_1e8_of_values

/-- LEAF: Schoenfeld 1976 p. 340, the Brent [3], [4] range. HARD.
From Brent's Table 1, `[li p + 1/2] - π p ≤ 4612` for primes `p ≤ 50·10⁸`, and the
display `|π x - li x| ≤ [li p + 1/2] - {π p - 1} + 1/2 ≤ 4613.5` for
`5·10⁷ ≤ x ≤ 49·10⁸` with `p` the least prime above `x`. -/
theorem brent_range : ∀ x : ℝ, 5 * 10 ^ 7 ≤ x → x ≤ 49 * 10 ^ 8 →
    |primeCount x - liPV x| ≤ 4613.5 := by
  exact LeanLab.BS2022GRH.BrentRangeS63.brent_range_glue

/-- LEAF: Schoenfeld 1976 display (6.20), from the Appel-Rosser table. MEDIUM.
`0 < {li x - π x} log x / √x < 2.523` for `3169 ≤ x ≤ 5·10⁷`. -/
theorem display_6_20 : ∀ x : ℝ, 3169 ≤ x → x ≤ 5 * 10 ^ 7 →
    0 < (liPV x - primeCount x) * log x / √x ∧
      (liPV x - primeCount x) * log x / √x < 2.523 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, (6.20) with 2.523 replaced by 2.444. MEDIUM.
`0 < {li x - π x} log x / √x < 2.444` for `2659 ≤ x < 3169`. S70: now proved in
`SchoenfeldFiniteS70` from its LEAF `table_6_20_low_int`, the table at the integers. -/
theorem display_6_20_low : ∀ x : ℝ, 2659 ≤ x → x < 3169 →
    0 < (liPV x - primeCount x) * log x / √x ∧
      (liPV x - primeCount x) * log x / √x < 2.444 := by
  exact LeanLab.BS2022GRH.SchoenfeldFiniteS70.display_6_20_low_of_leaf

/-- LEAF: Schoenfeld 1976 p. 340, "A direct calculation shows that (6.18) holds for
2,657 ≤ x < 2,659". MEDIUM. S70: now proved in `SchoenfeldFiniteS70` from its single
numerical LEAF, the enclosure `399.59 ≤ li 2657 ≤ 399.61`. -/
theorem direct_2657 : ∀ x : ℝ, 2657 ≤ x → x < 2659 →
    |primeCount x - liPV x| < √x * log x / (8 * π) := by
  exact LeanLab.BS2022GRH.SchoenfeldFiniteS70.direct_2657_of_leaf

/-! ### Proved glue -/

/-- `a ≤ log x` once `exp a ≤ c ≤ x`. -/
lemma le_log_of_exp_le {a c x : ℝ} (h : exp a ≤ c) (hx : c ≤ x) : a ≤ log x := by
  have hc : 0 < c := lt_of_lt_of_le (exp_pos a) h
  rw [le_log_iff_exp_le (by linarith)]; linarith

lemma exp_eight_lt : exp 8 < 2981 := by
  have h : exp 8 = exp 1 ^ 8 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have h1 := exp_one_lt_d9
  have h0 := exp_pos 1
  calc exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 := by gcongr
    _ < 2981 := by norm_num

/-- `exp (8 - t) ≤ exp 8 / (1 + t)`. -/
lemma exp_sub_le (t : ℝ) (ht : 0 ≤ t) : exp (8 - t) ≤ exp 8 / (1 + t) := by
  rw [exp_sub, div_le_div_iff_of_pos_left (exp_pos 8) (exp_pos t) (by linarith)]
  linarith [add_one_le_exp t]

lemma log_ge_797 {x : ℝ} (hx : 3169 ≤ x) : 7.97 ≤ log x := by
  refine le_log_of_exp_le (c := 3169) ?_ hx
  have h := exp_sub_le 0.03 (by norm_num)
  have e : (8 : ℝ) - 0.03 = 7.97 := by norm_num
  rw [e] at h
  have := exp_eight_lt
  calc exp 7.97 ≤ exp 8 / (1 + 0.03) := h
    _ ≤ 2981 / (1 + 0.03) := by gcongr
    _ ≤ 3169 := by norm_num

lemma log_ge_784 {x : ℝ} (hx : 2659 ≤ x) : 7.84 ≤ log x := by
  refine le_log_of_exp_le (c := 2659) ?_ hx
  have h := exp_sub_le 0.16 (by norm_num)
  have e : (8 : ℝ) - 0.16 = 7.84 := by norm_num
  rw [e] at h
  have := exp_eight_lt
  calc exp 7.84 ≤ exp 8 / (1 + 0.16) := h
    _ ≤ 2981 / (1 + 0.16) := by gcongr
    _ ≤ 2659 := by norm_num

lemma log_ge_17 {x : ℝ} (hx : 5 * 10 ^ 7 ≤ x) : 17 ≤ log x := by
  refine le_log_of_exp_le (c := 5 * 10 ^ 7) ?_ hx
  have h : exp 17 = exp 1 ^ 17 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have h1 := exp_one_lt_d9
  have h0 := exp_pos 1
  calc exp 1 ^ 17 ≤ (2.7182818286 : ℝ) ^ 17 := by gcongr
    _ ≤ 5 * 10 ^ 7 := by norm_num

/-- From a table bound `0 < d log x / √x < c` with `8 π c ≤ log² x`, (6.18) follows. -/
lemma of_table {x c d : ℝ} (hx : 1 < x) (h0 : 0 < d * log x / √x) (h1 : d * log x / √x < c)
    (hc : c * (8 * 3.1416) ≤ log x ^ 2) : |-d| < √x * log x / (8 * π) := by
  have hl : 0 < log x := log_pos hx
  have hs : 0 < √x := sqrt_pos.mpr (by linarith)
  have hpi : π < 3.1416 := pi_lt_d4
  have hpi0 : 0 < π := pi_pos
  have hd : 0 < d := by
    by_contra hneg; rw [not_lt] at hneg
    have : d * log x / √x ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hneg hl.le) hs.le
    linarith
  rw [abs_neg, abs_of_pos hd, lt_div_iff₀ (by positivity)]
  rw [div_lt_iff₀ hs] at h1
  have hc0 : 0 < c := by
    have : 0 < d * log x := mul_pos hd hl
    nlinarith
  -- d log x < c √x, so d log x * 8π < c √x * 8 * 3.1416 ≤ √x log² x
  have h2 : d * log x * (8 * π) < c * √x * (8 * 3.1416) := by
    have : d * log x * (8 * π) ≤ d * log x * (8 * 3.1416) := by
      have : 0 < d * log x := mul_pos hd hl
      nlinarith
    nlinarith
  have h3 : c * √x * (8 * 3.1416) ≤ √x * log x * log x := by nlinarith
  have h4 : d * (8 * π) * log x < √x * log x * log x := by nlinarith
  exact lt_of_mul_lt_mul_right h4 hl.le

/-- (6.18) on `3169 ≤ x ≤ 5·10⁷`, from (6.20). -/
theorem range_3169 (x : ℝ) (h1 : 3169 ≤ x) (h2 : x ≤ 5 * 10 ^ 7) :
    |primeCount x - liPV x| < √x * log x / (8 * π) := by
  obtain ⟨a, b⟩ := display_6_20 x h1 h2
  have hl := log_ge_797 h1
  have e : primeCount x - liPV x = -(liPV x - primeCount x) := by ring
  rw [e]
  exact of_table (by linarith) a b (by nlinarith)

/-- (6.18) on `2659 ≤ x < 3169`, from the 2.444 form of (6.20). -/
theorem range_2659 (x : ℝ) (h1 : 2659 ≤ x) (h2 : x < 3169) :
    |primeCount x - liPV x| < √x * log x / (8 * π) := by
  obtain ⟨a, b⟩ := display_6_20_low x h1 h2
  have hl := log_ge_784 h1
  have e : primeCount x - liPV x = -(liPV x - primeCount x) := by ring
  rw [e]
  exact of_table (by linarith) a b (by nlinarith)

/-- (6.18) on `5·10⁷ ≤ x ≤ 49·10⁸`, from the Brent range: `4613.5 < √x log x / (8π)`. -/
theorem range_brent (x : ℝ) (h1 : 5 * 10 ^ 7 ≤ x) (h2 : x ≤ 49 * 10 ^ 8) :
    |primeCount x - liPV x| < √x * log x / (8 * π) := by
  have hb := brent_range x h1 h2
  have hl := log_ge_17 h1
  have hs : 7071 ≤ √x := by
    rw [le_sqrt (by norm_num) (by linarith)]; linarith
  have hpi : π < 3.1416 := pi_lt_d4
  have hpi0 : 0 < π := pi_pos
  rw [lt_div_iff₀ (by positivity)]
  have : 7071 * 17 ≤ √x * log x := by nlinarith
  nlinarith

/-- The display after (6.19b): for `x ≥ ξ > 1`,
`π x - li x = (θ x - x)/log x + ∫_ξ^x (θ y - y)/(y log² y) dy - ξ'`,
from (6.19a) and [10, (7.6)]. -/
theorem display_after_6_19b (ξ x : ℝ) (hξ : 1 < ξ) (hx : ξ ≤ x) :
    primeCount x - liPV x = (Chebyshev.theta x - x) / log x
      + (∫ y in ξ..x, (Chebyshev.theta y - y) / (y * log y ^ 2)) - xiPrime ξ := by
  have hA := display_6_19a ξ x hξ hx
  have hB := rs62_7_6 ξ x hξ hx
  have hsub : uIcc ξ x ⊆ Ioi 1 := by
    intro y hy; rw [uIcc_of_le hx] at hy; exact lt_of_lt_of_le hξ hy.1
  have hcont : ContinuousOn (fun y : ℝ => 1 / (y * log y ^ 2)) (uIcc ξ x) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_id.mul ((continuousOn_log.mono (fun y hy => by
        have := hsub hy; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt
          (lt_trans one_pos this))).pow 2)
    · intro y hy
      have h1 : 1 < y := hsub hy
      have : 0 < log y := log_pos h1
      positivity
  have hI1 : IntervalIntegrable (fun y => Chebyshev.theta y / (y * log y ^ 2)) volume ξ x := by
    have hm : IntervalIntegrable Chebyshev.theta volume ξ x :=
      Chebyshev.theta_mono.intervalIntegrable
    have := hm.mul_continuousOn hcont
    refine this.congr (fun y _ => ?_)
    simp [div_eq_mul_inv]
  have hc2 : ContinuousOn (fun y : ℝ => 1 / log y ^ 2) (uIcc ξ x) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuousOn_log.mono (fun y hy => by
        have := hsub hy; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt
          (lt_trans one_pos this))).pow 2
    · intro y hy
      have : 0 < log y := log_pos (hsub hy)
      positivity
  have hI2 : IntervalIntegrable (fun y : ℝ => 1 / log y ^ 2) volume ξ x :=
    hc2.intervalIntegrable
  have hdiff : (∫ y in ξ..x, (Chebyshev.theta y - y) / (y * log y ^ 2)) =
      (∫ y in ξ..x, Chebyshev.theta y / (y * log y ^ 2)) - ∫ y in ξ..x, 1 / log y ^ 2 := by
    rw [← integral_sub hI1 hI2]
    refine integral_congr (fun y hy => ?_)
    have h1 : 1 < y := hsub hy
    have hy0 : y ≠ 0 := by linarith
    have hl : log y ≠ 0 := (log_pos h1).ne'
    field_simp
  rw [hdiff]
  unfold xiPrime
  have hl : log ξ ≠ 0 := (log_pos hξ).ne'
  have hlx : log x ≠ 0 := (log_pos (lt_of_lt_of_le hξ hx)).ne'
  have e1 : (Chebyshev.theta x - x) / log x = Chebyshev.theta x / log x - x / log x := by
    rw [sub_div]
  have e2 : (ξ - Chebyshev.theta ξ) / log ξ = ξ / log ξ - Chebyshev.theta ξ / log ξ := by
    rw [sub_div]
  rw [e1, e2]
  linarith

/-- `∫_ξ^x 1/(8π√y) dy = (√x - √ξ)/(4π)` for `0 < ξ ≤ x`. -/
lemma integral_inv_sqrt {ξ x : ℝ} (hξ : 0 < ξ) (hx : ξ ≤ x) :
    ∫ y in ξ..x, 1 / (8 * π * √y) = (√x - √ξ) / (4 * π) := by
  have hpi : 0 < π := pi_pos
  have key : ∀ y ∈ uIcc ξ x, HasDerivAt (fun y => √y / (4 * π)) (1 / (8 * π * √y)) y := by
    intro y hy
    rw [uIcc_of_le hx] at hy
    have hy0 : 0 < y := lt_of_lt_of_le hξ hy.1
    have h := (hasDerivAt_sqrt hy0.ne').div_const (4 * π)
    convert h using 1
    have : 0 < √y := sqrt_pos.mpr hy0
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt key]
  · ring
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_const.mul continuous_sqrt.continuousOn
    · intro y hy
      rw [uIcc_of_le hx] at hy
      have : 0 < √y := sqrt_pos.mpr (lt_of_lt_of_le hξ hy.1)
      positivity

/-- (6.18) for `x ≥ 23·10⁸` under RH: the estimate after (6.19b) with (6.1), (6.3)
and `ξ = 10⁸`, where `|ξ'| < 89 < √ξ / (4π)`. -/
theorem range_large (hRH : RiemannHypothesis) (x : ℝ) (hx : 23 * 10 ^ 8 ≤ x) :
    |primeCount x - liPV x| < √x * log x / (8 * π) := by
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℝ, ξ = 10 ^ 8 := ⟨_, rfl⟩
  have hξ1 : 1 < ξ := by norm_num [hξdef]
  have hξx : ξ ≤ x := by rw [hξdef]; linarith
  have hpi : 0 < π := pi_pos
  have hpi4 : π < 3.1416 := pi_lt_d4
  have hx1 : 1 < x := by linarith
  have hl : 0 < log x := log_pos hx1
  have hsx : 0 < √x := sqrt_pos.mpr (by linarith)
  rw [display_after_6_19b ξ x hξ1 hξx]
  -- first term
  have hT1 : |(Chebyshev.theta x - x) / log x| < √x * (log x - 2) / (8 * π) := by
    rw [abs_div, abs_of_pos hl, div_lt_iff₀ hl]
    have := thm10_61 hRH x hx
    calc |Chebyshev.theta x - x| < √x * (log x - 2) * log x / (8 * π) := this
      _ = √x * (log x - 2) / (8 * π) * log x := by ring
  -- integral term
  have hT2 : |∫ y in ξ..x, (Chebyshev.theta y - y) / (y * log y ^ 2)| ≤ (√x - √ξ) / (4 * π) := by
    rw [← integral_inv_sqrt (by linarith) hξx, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hξx ?_ ?_
    · filter_upwards with y hy
      have hy599 : 599 ≤ y := by
        have : ξ < y := hy.1
        rw [hξdef] at this; linarith
      have hy1 : 1 < y := by linarith
      have hly : 0 < log y := log_pos hy1
      have hsy : 0 < √y := sqrt_pos.mpr (by linarith)
      have hb := thm10_63 hRH y hy599
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y * log y ^ 2),
        div_le_iff₀ (by positivity)]
      have hyy : y / √y = √y := div_sqrt
      have : 1 / (8 * π * √y) * (y * log y ^ 2) = √y * log y ^ 2 / (8 * π) := by
        calc 1 / (8 * π * √y) * (y * log y ^ 2) = (y / √y) * log y ^ 2 / (8 * π) := by ring
          _ = √y * log y ^ 2 / (8 * π) := by rw [hyy]
      rw [this]; exact hb.le
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact continuousOn_const.mul continuous_sqrt.continuousOn
      · intro y hy
        rw [uIcc_of_le hξx] at hy
        have : 0 < √y := sqrt_pos.mpr (by linarith [hy.1])
        positivity
  have hT3 : |xiPrime ξ| < 89 := by rw [hξdef]; exact xiPrime_1e8
  have hsξ : √ξ = 10 ^ 4 := by
    rw [hξdef, show (10 : ℝ) ^ 8 = (10 ^ 4) ^ 2 by norm_num]
    exact sqrt_sq (by norm_num)
  rw [hsξ] at hT2
  have habs := abs_sub (((Chebyshev.theta x - x) / log x)
    + ∫ y in ξ..x, (Chebyshev.theta y - y) / (y * log y ^ 2)) (xiPrime ξ)
  have habs2 := abs_add_le (((Chebyshev.theta x - x) / log x))
    (∫ y in ξ..x, (Chebyshev.theta y - y) / (y * log y ^ 2))
  have hgoal : √x * (log x - 2) / (8 * π) + (√x - 10 ^ 4) / (4 * π) + 89 ≤
      √x * log x / (8 * π) := by
    have e : √x * (log x - 2) / (8 * π) + (√x - 10 ^ 4) / (4 * π) + 89 =
        √x * log x / (8 * π) - (10 ^ 4 / (4 * π) - 89) := by
      field_simp; ring
    rw [e]
    have : 89 ≤ 10 ^ 4 / (4 * π) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  calc _ ≤ _ := habs
    _ ≤ |(Chebyshev.theta x - x) / log x|
        + |∫ y in ξ..x, (Chebyshev.theta y - y) / (y * log y ^ 2)| + |xiPrime ξ| := by
          linarith
    _ < √x * (log x - 2) / (8 * π) + (√x - 10 ^ 4) / (4 * π) + 89 := by linarith
    _ ≤ _ := hgoal

/-- **Schoenfeld 1976 Corollary 1, display (6.18)**, assembled from the leaves above:
the statement `PaperInputs148.Lemma1J`. CONDITIONAL ON the cited leaves of this file. -/
theorem cor1_6_18 : PaperInputs148.Lemma1J := by
  intro hRH x hx
  refine le_of_lt ?_
  by_cases h1 : x < 2659
  · exact direct_2657 x hx h1
  by_cases h2 : x < 3169
  · exact range_2659 x (by linarith) h2
  by_cases h3 : x ≤ 5 * 10 ^ 7
  · exact range_3169 x (by linarith) h3
  by_cases h4 : x ≤ 49 * 10 ^ 8
  · exact range_brent x (by linarith) h4
  exact range_large hRH x (by linarith)

end

end LeanLab.BS2022GRH.SchoenfeldCor1S63

#print axioms LeanLab.BS2022GRH.SchoenfeldCor1S63.rs62_7_6
#print axioms LeanLab.BS2022GRH.SchoenfeldCor1S63.display_after_6_19b
#print axioms LeanLab.BS2022GRH.SchoenfeldCor1S63.integral_inv_sqrt
#print axioms LeanLab.BS2022GRH.SchoenfeldCor1S63.range_large
#print axioms LeanLab.BS2022GRH.SchoenfeldCor1S63.range_brent
#print axioms LeanLab.BS2022GRH.SchoenfeldCor1S63.range_3169
#print axioms LeanLab.BS2022GRH.SchoenfeldCor1S63.range_2659
#print axioms LeanLab.BS2022GRH.SchoenfeldCor1S63.cor1_6_18
