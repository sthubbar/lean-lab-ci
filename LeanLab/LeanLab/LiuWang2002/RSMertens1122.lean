/-
Burst burst-20261122, session S78, target LiuWang2002. Split of the cited input
`U1543.rs2_mertens` of Decomp1543b.lean, Liu-Wang 2002 p. 172, which cites Rosser-Schoenfeld
1962, Illinois J. Math. 6, p. 70 Theorem 6, displays (3.21) and (3.22), with E of (2.11) p. 65:
for `x ≥ 15000`, `log x - 1.385 ≤ Σ_{p≤x} log p / p ≤ log x - 1.28`.
Source: papers/RosserSchoenfeld1962.pdf, pages 65, 70, 72 and 87, read on the page images.
RS prove Theorem 6, p. 87, by the Rosser-Walker tabulation below 16000, by the machine
tabulation behind Theorems 18 and 21 on `[16000, 10^8]`, and by a Lemma 13 analogue above 10^8.
This file follows that split:
* `abel_G`, PROVED, no input: with `G x = Σ_{p≤x} log p/p - log x` and `R t = θ t - t`,
  `G b - G a = R b/b - R a/a + ∫_a^b R t/t² dt`, the identity behind RS (4.13).
* `G_window`, PROVED: if `-K√t ≤ R t ≤ 0` on `[a, b]` then `-2K/√a ≤ G b - G a ≤ K/√a`.
* `G_diff_dusart`, CONDITIONAL ON `DusartThm52k2`: `|G b - G a| ≤ 0.001` for `10^10 ≤ a ≤ b`.
* `rs2_mertens_of_inputs`, CONDITIONAL ON the four inputs below, all named as hypotheses.
* LEAFs: RS Theorem 18 display (4.5); RS Theorem 21 display (4.8) at `x = 15000`;
  RS Theorem 6 on `[10^8, 10^10]`; Dusart 2010 Theorem 5.2 row k = 2, the lab's `DusartThm52k2`.
* `rs2_mertens_split`: the statement of `U1543.rs2_mertens`, from the LEAFs.
AI-written Lean code, Claude, 2026-11-22. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.AlmostPrimes.MertensRS320
import LeanLab.LiuWang2002.RSMertens15000

open Real Finset Filter MeasureTheory

noncomputable section
namespace LeanLab.LiuWang2002.RSMertens1122

open LeanLab.AlmostPrimes.MertensRS320 (R c sum_c seventeen_le_log)
open LeanLab.Common.ThetaWindow (DusartThm52k2)

/-- `Σ_{a<k≤b} k⁻¹ c k` is the difference of the prime sums `Σ log p / p`. -/
theorem T_sub {a b : ℝ} (hab : a ≤ b) :
    (∑ p ∈ (range (⌊b⌋₊ + 1)).filter Nat.Prime, Real.log p / p) -
      (∑ p ∈ (range (⌊a⌋₊ + 1)).filter Nat.Prime, Real.log p / p) =
      ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (k : ℝ)⁻¹ * c k := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hterm : ∀ k : ℕ, (k : ℝ)⁻¹ * c k = if k.Prime then Real.log k / k else 0 := by
    intro k
    unfold c
    split_ifs with hk
    · rw [inv_mul_eq_div]
    · simp
  simp_rw [hterm]
  rw [sum_filter, sum_filter, range_eq_Ico, range_eq_Ico, ← Ico_add_one_add_one_eq_Ioc]
  rw [← sum_Ico_consecutive _ (Nat.zero_le (⌊a⌋₊ + 1)) (by omega : ⌊a⌋₊ + 1 ≤ ⌊b⌋₊ + 1)]
  ring

theorem q_cont {a b : ℝ} (ha : 0 < a) : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have ht2 : t ^ 2 ≠ 0 := by positivity
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := assumption)

theorem qR_int {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (t ^ 2)⁻¹ * R t) volume a b := by
  have h1 : IntervalIntegrable (fun t => (t ^ 2)⁻¹ * Chebyshev.theta t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have := integrableOn_mul_sum_Icc c (m := 0) (by linarith : (0 : ℝ) ≤ a)
      ((q_cont (b := b) (by linarith : (0 : ℝ) < a)).integrableOn_Icc)
    simpa only [sum_c] using this
  have h2 : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹ * t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact (q_cont (by linarith)).mul continuousOn_id
  refine (h1.sub h2).congr ?_
  intro t _
  simp only [R]; ring

/-- **Abel summation for `Σ log p / p`**, PROVED, no cited input. With `R t = θ t - t`,
`G b - G a = R b/b - R a/a + ∫_a^b R t/t² dt` where `G x = Σ_{p≤x} log p/p - log x`.
This is the partial summation of Rosser-Schoenfeld 1962 (4.13) with `f(y) = 1/y`. -/
theorem abel_G {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ((∑ p ∈ (range (⌊b⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log b) -
      ((∑ p ∈ (range (⌊a⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log a) =
      R b / b - R a / a + ∫ t in a..b, (t ^ 2)⁻¹ * R t := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hb1 : (1 : ℝ) < b := by linarith
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t :=
    fun t ht => differentiableAt_inv (by linarith [ht.1])
  have hder : ∀ t ∈ Set.Icc a b, deriv (fun t : ℝ => t⁻¹) t = -(t ^ 2)⁻¹ :=
    fun t _ => deriv_inv
  have hint : IntegrableOn (deriv fun t : ℝ => t⁻¹) (Set.Icc a b) := by
    have h1 : IntegrableOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc a b) :=
      ((q_cont (b := b) (by linarith : (0 : ℝ) < a)).neg).integrableOn_Icc
    exact h1.congr_fun (fun t ht => (hder t ht).symm) measurableSet_Icc
  have hA := sum_mul_eq_sub_sub_integral_mul c ha0 hab hdiff hint
  rw [sum_c, sum_c] at hA
  have hI : ∫ t in Set.Ioc a b, deriv (fun t : ℝ => t⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
      -∫ t in a..b, (t ^ 2)⁻¹ * Chebyshev.theta t := by
    rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    simp only [sum_c, hder t ht]
    ring
  rw [hI] at hA
  have hq_id : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹ * t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact (q_cont (by linarith)).mul continuousOn_id
  have hsplit : ∫ t in a..b, (t ^ 2)⁻¹ * Chebyshev.theta t =
      (∫ t in a..b, (t ^ 2)⁻¹ * t) + ∫ t in a..b, (t ^ 2)⁻¹ * R t := by
    rw [← intervalIntegral.integral_add hq_id (qR_int ha hab)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [R]; ring
  have hlog : ∫ t in a..b, (t ^ 2)⁻¹ * t = Real.log b - Real.log a := by
    have he : ∫ t in a..b, (t ^ 2)⁻¹ * t = ∫ t in a..b, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      field_simp
    rw [he, integral_inv_of_pos (by linarith) (by linarith),
      Real.log_div (by linarith) (by linarith)]
  rw [hsplit, hlog] at hA
  have hT := T_sub hab
  have ha0' : a ≠ 0 := by linarith
  have hb0' : b ≠ 0 := by linarith
  have eb : b⁻¹ * Chebyshev.theta b = 1 + R b / b := by
    unfold R; field_simp; ring
  have ea : a⁻¹ * Chebyshev.theta a = 1 + R a / a := by
    unfold R; field_simp; ring
  rw [eb, ea] at hA
  linarith

/-- `√t / t² = 1/(t √t)` for `t > 0`. -/
theorem sqrt_div_sq {t : ℝ} (ht : 0 < t) : (t ^ 2)⁻¹ * √t = (t * √t)⁻¹ := by
  have hs : 0 < √t := Real.sqrt_pos.mpr ht
  have hss : √t * √t = t := Real.mul_self_sqrt ht.le
  field_simp
  nlinarith [hss]

/-- `∫_a^b (t √t)⁻¹ dt = 2/√a - 2/√b`. -/
theorem integral_inv_t_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, (t * √t)⁻¹ = 2 * (√a)⁻¹ - 2 * (√b)⁻¹ := by
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => -(2 * (√t)⁻¹)) (f' := fun t => (t * √t)⁻¹) (a := a) (b := b) ?_ ?_
  · rw [key]; ring
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs : 0 < √t := Real.sqrt_pos.mpr ht0
    have hss : √t * √t = t := Real.mul_self_sqrt ht0.le
    have h := ((Real.hasDerivAt_sqrt ht0.ne').inv hs.ne').const_mul (2 : ℝ)
    have h' := h.neg
    convert h' using 1
    field_simp
    first | ring | linarith [Real.sq_sqrt ht0.le] | nlinarith [Real.sq_sqrt ht0.le, hss]
    all_goals exact Real.sq_sqrt ht0.le
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs : 0 < √t := Real.sqrt_pos.mpr ht0
    have hne : t * √t ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    exact ((continuousAt_id.mul Real.continuous_sqrt.continuousAt)).inv₀ hne

/-- **Window lemma**, PROVED, no cited input: if `-K√t ≤ θ t - t ≤ 0` on `[a, b]`, then
`-2K/√a ≤ G b - G a ≤ K/√a`. The step RS use with Theorem 18 between tabulated points. -/
theorem G_window {a b K : ℝ} (ha : 1 < a) (hab : a ≤ b) (hK : 0 ≤ K)
    (hR : ∀ t ∈ Set.Icc a b, -(K * √t) ≤ R t ∧ R t ≤ 0) :
    -(2 * K / √a) ≤
        ((∑ p ∈ (range (⌊b⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log b) -
          ((∑ p ∈ (range (⌊a⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log a) ∧
      ((∑ p ∈ (range (⌊b⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log b) -
          ((∑ p ∈ (range (⌊a⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log a) ≤
        K / √a := by
  rw [abel_G ha hab]
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha0
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb0
  have hssa : √a * √a = a := Real.mul_self_sqrt ha0.le
  have hssb : √b * √b = b := Real.mul_self_sqrt hb0.le
  obtain ⟨hRb1, hRb2⟩ := hR b ⟨hab, le_refl b⟩
  obtain ⟨hRa1, hRa2⟩ := hR a ⟨le_refl a, hab⟩
  -- boundary terms
  have hb1 : -(K / √b) ≤ R b / b := by
    rw [le_div_iff₀ hb0]
    have : -(K / √b) * b = -(K * √b) := by
      field_simp
      first | linear_combination K * hssb | linear_combination (-K) * hssb |
        linear_combination hssb | linear_combination (-1 : ℝ) * hssb
    linarith
  have hb2 : R b / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg hRb2 hb0.le
  have ha1 : 0 ≤ -(R a / a) := by
    have := div_nonpos_of_nonpos_of_nonneg hRa2 ha0.le; linarith
  have ha2 : -(R a / a) ≤ K / √a := by
    rw [neg_le, le_div_iff₀ ha0]
    have : -(K / √a) * a = -(K * √a) := by
      field_simp
      first | linear_combination K * hssa | linear_combination (-K) * hssa |
        linear_combination hssa | linear_combination (-1 : ℝ) * hssa
    linarith
  -- integral term
  have hint := qR_int ha hab
  have hI2 : ∫ t in a..b, (t ^ 2)⁻¹ * R t ≤ 0 := by
    have := intervalIntegral.integral_mono_on hab hint
      (intervalIntegrable_const (c := (0 : ℝ))) (fun t ht => by
        have ht0 : 0 < t := by linarith [ht.1]
        have := (hR t ht).2
        have hq : 0 ≤ (t ^ 2)⁻¹ := by positivity
        nlinarith)
    simpa using this
  have hcont : IntervalIntegrable (fun t => -K * (t * √t)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs : 0 < √t := Real.sqrt_pos.mpr ht0
    have hne : t * √t ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.mul
      (((continuousAt_id.mul Real.continuous_sqrt.continuousAt)).inv₀ hne)
  have hI1 : ∫ t in a..b, -K * (t * √t)⁻¹ ≤ ∫ t in a..b, (t ^ 2)⁻¹ * R t := by
    apply intervalIntegral.integral_mono_on hab hcont hint
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hq : 0 ≤ (t ^ 2)⁻¹ := by positivity
    have h1 := (hR t ht).1
    calc -K * (t * √t)⁻¹ = (t ^ 2)⁻¹ * -(K * √t) := by rw [← sqrt_div_sq ht0]; ring
      _ ≤ (t ^ 2)⁻¹ * R t := mul_le_mul_of_nonneg_left h1 hq
  have hval : ∫ t in a..b, -K * (t * √t)⁻¹ = -K * (2 * (√a)⁻¹ - 2 * (√b)⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_t_sqrt ha0 hab]
  rw [hval] at hI1
  have hKb : 0 ≤ K / √b := div_nonneg hK hsb.le
  have e1 : K / √b = K * (√b)⁻¹ := div_eq_mul_inv _ _
  have e2 : K / √a = K * (√a)⁻¹ := div_eq_mul_inv _ _
  have e3 : 2 * K / √a = 2 * (K * (√a)⁻¹) := by rw [mul_div_assoc, e2]
  constructor
  · rw [e3]; rw [e1] at hb1 hKb; rw [e2] at ha2; nlinarith
  · linarith

/-- `log x ≥ 17` for `x ≥ 10^8`. -/
theorem seventeen_le_log_1e8 {z : ℝ} (hz : 10 ^ 8 ≤ z) : 17 ≤ Real.log z := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h : Real.exp 1 ^ 17 ≤ (2.7182818286 : ℝ) ^ 17 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 17
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  have h2 : (2.7182818286 : ℝ) ^ 17 ≤ 10 ^ 8 := by norm_num
  linarith

/-- `∫_a^b 0.01/(t log² t) dt = 0.01/log a - 0.01/log b`. -/
theorem integral_dusart {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 0.01 * (t * Real.log t ^ 2)⁻¹ = 0.01 * (Real.log a)⁻¹ - 0.01 * (Real.log b)⁻¹ := by
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => -(0.01 * (Real.log t)⁻¹)) (f' := fun t => 0.01 * (t * Real.log t ^ 2)⁻¹)
    (a := a) (b := b) ?_ ?_
  · rw [key]; ring
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have h := (((Real.hasDerivAt_log ht0).inv hl).const_mul (0.01 : ℝ)).neg
    convert h using 1
    field_simp
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have : t * Real.log t ^ 2 ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)

/-- **Tail step**, CONDITIONAL ON `DusartThm52k2`: `|G b - G a| ≤ 0.001` for `10^10 ≤ a ≤ b`. -/
theorem G_diff_dusart (hD : DusartThm52k2) {a b : ℝ} (ha : 10 ^ 10 ≤ a) (hab : a ≤ b) :
    |((∑ p ∈ (range (⌊b⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log b) -
      ((∑ p ∈ (range (⌊a⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log a)| ≤ 0.001 := by
  have ha1 : (1 : ℝ) < a := by linarith
  rw [abel_G ha1 hab]
  have hLa := seventeen_le_log ha
  have hLb := seventeen_le_log (le_trans ha hab)
  have hbound : ∀ t : ℝ, 10 ^ 10 ≤ t → |R t / t| ≤ 0.01 / 289 := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hL := seventeen_le_log ht
    have hRt := hD t (by linarith)
    rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    have hl2 : (289 : ℝ) ≤ Real.log t ^ 2 := by nlinarith
    have : 0.01 * t / Real.log t ^ 2 ≤ 0.01 / 289 * t := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    simpa [R] using hRt.trans this
  have e1 := hbound b (le_trans ha hab)
  have e2 := hbound a ha
  have hint := qR_int ha1 hab
  have hcont : IntervalIntegrable (fun t => 0.01 * (t * Real.log t ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have : t * Real.log t ^ 2 ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have h1 := intervalIntegral.abs_integral_le_integral_abs (f := fun t => (t ^ 2)⁻¹ * R t)
    (μ := volume) hab
  have h2 : ∫ t in a..b, |(t ^ 2)⁻¹ * R t| ≤ ∫ t in a..b, 0.01 * (t * Real.log t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hab hint.abs hcont
    intro t ht
    have ht' : 7713133853 ≤ t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    have hRt := hD t ht'
    have hq : 0 ≤ (t ^ 2)⁻¹ := by positivity
    rw [abs_mul, abs_of_nonneg hq]
    calc (t ^ 2)⁻¹ * |R t| ≤ (t ^ 2)⁻¹ * (0.01 * t / Real.log t ^ 2) :=
          mul_le_mul_of_nonneg_left (by simpa [R] using hRt) hq
      _ = 0.01 * (t * Real.log t ^ 2)⁻¹ := by field_simp
  have h3 := integral_dusart ha1 hab
  have hLb0 : 0 ≤ 0.01 * (Real.log b)⁻¹ := by positivity
  have hLa' : (Real.log a)⁻¹ ≤ (17 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hLa
  have hsum : |R b / b - R a / a + ∫ t in a..b, (t ^ 2)⁻¹ * R t| ≤
      |R b / b| + |R a / a| + |∫ t in a..b, (t ^ 2)⁻¹ * R t| := by
    have := abs_add_le (R b / b - R a / a) (∫ t in a..b, (t ^ 2)⁻¹ * R t)
    have := abs_sub (R b / b) (R a / a)
    linarith
  linarith

/-- **Assembly**, CONDITIONAL ON the four named inputs `h18`, `h15000`, `h6mid`, `hD`:
the statement of `U1543.rs2_mertens`. On `[15000, 10^8]` by `G_window` with RS Theorem 18,
`K = 2.05282`, from the value at 15000; on `[10^8, 10^10]` by RS Theorem 6 there; above
`10^10` by `G_diff_dusart` from the value at `10^10`. -/
theorem rs2_mertens_of_inputs
    (h18 : ∀ x : ℝ, 0 < x → x ≤ 10 ^ 8 →
      x - 2.05282 * √x < Chebyshev.theta x ∧ Chebyshev.theta x < x)
    (h15000 : -1.35 ≤ (∑ p ∈ (range (⌊(15000 : ℝ)⌋₊ + 1)).filter Nat.Prime,
        Real.log p / p) - Real.log 15000 ∧
      (∑ p ∈ (range (⌊(15000 : ℝ)⌋₊ + 1)).filter Nat.Prime, Real.log p / p) -
        Real.log 15000 ≤ -1.30)
    (h6mid : ∀ x : ℝ, 10 ^ 8 ≤ x → x ≤ 10 ^ 10 →
      Real.log x - 1.33259 - 1 / (2 * Real.log x) ≤
          ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ∧
        ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ≤
          Real.log x - 1.33258 + 1 / (2 * Real.log x))
    (hD : DusartThm52k2) (x : ℝ) (hx : 15000 ≤ x) :
    Real.log x - 1.385 ≤ ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ∧
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ≤ Real.log x - 1.28 := by
  -- the RS Theorem 6 band at a point of `[10^8, 10^10]`
  have hmid : ∀ y : ℝ, 10 ^ 8 ≤ y → y ≤ 10 ^ 10 →
      -1.3621 ≤ (∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log y ∧
      (∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log y ≤ -1.3031 := by
    intro y hy1 hy2
    have hL := seventeen_le_log_1e8 hy1
    have hinv : 1 / (2 * Real.log y) ≤ 1 / 34 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    obtain ⟨l, u⟩ := h6mid y hy1 hy2
    constructor <;> linarith
  rcases le_or_gt x (10 ^ 8) with hx8 | hx8
  · -- window from 15000
    have hW := G_window (a := 15000) (b := x) (K := 2.05282) (by norm_num) hx (by norm_num)
      (fun t ht => by
        have ht0 : 0 < t := by linarith [ht.1]
        obtain ⟨l, u⟩ := h18 t ht0 (le_trans ht.2 hx8)
        constructor <;> simp only [R] <;> linarith)
    have h122 : (122 : ℝ) ≤ √15000 := by
      rw [show (122 : ℝ) = √(122 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hK1 : 2.05282 / √15000 ≤ 2.05282 / 122 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h122
    have hK2 : 2 * 2.05282 / √15000 ≤ 2 * 2.05282 / 122 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h122
    obtain ⟨l0, u0⟩ := h15000
    obtain ⟨lW, uW⟩ := hW
    constructor
    · have : (2 * 2.05282 / 122 : ℝ) ≤ 0.034 := by norm_num
      linarith
    · have : (2.05282 / 122 : ℝ) ≤ 0.017 := by norm_num
      linarith
  · rcases le_or_gt x (10 ^ 10) with hx10 | hx10
    · obtain ⟨l, u⟩ := hmid x hx8.le hx10
      constructor <;> linarith
    · obtain ⟨l, u⟩ := hmid (10 ^ 10) (by norm_num) le_rfl
      have hd := G_diff_dusart hD (le_refl (10 ^ 10 : ℝ)) hx10.le
      rw [abs_le] at hd
      obtain ⟨dl, du⟩ := hd
      constructor <;> linarith

/-! ### LEAFs, each a cited display -/

/-- LEAF: Rosser-Schoenfeld 1962 p. 72 Theorem 18 display (4.5), with its full printed domain
`0 < x ≤ 10^8`: `x - 2.05282 x^(1/2) < θ(x) < x`. Established by machine tabulation, p. 75.
Class HARD, finite computation to 10^8, cited wall. -/
theorem rs1962_thm18 (x : ℝ) (hx : 0 < x) (hx8 : x ≤ 10 ^ 8) :
    x - 2.05282 * √x < Chebyshev.theta x ∧ Chebyshev.theta x < x := by
  sorry

/-- LEAF: Rosser-Schoenfeld 1962 p. 72 Theorem 21 display (4.8) at `x = 15000`, with E of (2.11)
p. 65, `E = -1.33258 22757`: `log x + E < Σ_{p≤x} log p/p < log x + E + 2.06123/x^(1/2)`
places the value in `[-1.3326, -1.3157]`; the leaf asks only `[-1.35, -1.30]`.
Python over the 1754 primes below 15000 gives `-1.32403`. Class MEDIUM, a finite sum.
PROVED in RSMertens15000 by a kernel certificate, session S78. -/
theorem rs1962_thm21_at_15000 :
    -1.35 ≤ (∑ p ∈ (range (⌊(15000 : ℝ)⌋₊ + 1)).filter Nat.Prime, Real.log p / p) -
        Real.log 15000 ∧
      (∑ p ∈ (range (⌊(15000 : ℝ)⌋₊ + 1)).filter Nat.Prime, Real.log p / p) -
        Real.log 15000 ≤ -1.30 :=
  -- PROVED in RSMertens15000 by a kernel certificate, burst-20261122 S78.
  RSMertens15000.rs1962_thm21_at_15000

/-- LEAF: Rosser-Schoenfeld 1962 p. 70 Theorem 6 displays (3.21) and (3.22) on `[10^8, 10^10]`,
with E of (2.11) p. 65 enclosed as `-1.33259 ≤ E ≤ -1.33258`:
`log x + E - 1/(2 log x) < Σ_{p≤x} log p/p < log x + E + 1/(2 log x)`. RS prove this range,
p. 87, by the analogue of their Lemma 13 with Lemma 7. Class HARD, cited wall. -/
theorem rs1962_thm6_mid (x : ℝ) (hx : 10 ^ 8 ≤ x) (hx10 : x ≤ 10 ^ 10) :
    Real.log x - 1.33259 - 1 / (2 * Real.log x) ≤
        ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ∧
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ≤
        Real.log x - 1.33258 + 1 / (2 * Real.log x) := by
  sorry

/-- LEAF: Dusart 2010, arXiv 1002.0442, Theorem 5.2, row k = 2, η₂ = 0.01, x₂ = 7713133853:
`|θ(x) - x| < 0.01 x / log² x`, the lab's named input `Common.ThetaWindow.DusartThm52k2`.
Used here in place of the Rosser-Schoenfeld Lemma 13 analogue above `10^10`. Class HARD,
cited wall. -/
theorem dusart_thm52_k2 : DusartThm52k2 := by
  sorry

/-- The statement of `U1543.rs2_mertens`, Liu-Wang p. 172, from the four LEAFs above. -/
theorem rs2_mertens_split (x : ℝ) (hx : 15000 ≤ x) :
    Real.log x - 1.385 ≤ ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ∧
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ≤ Real.log x - 1.28 :=
  rs2_mertens_of_inputs rs1962_thm18 rs1962_thm21_at_15000 rs1962_thm6_mid dusart_thm52_k2 x hx

end LeanLab.LiuWang2002.RSMertens1122
