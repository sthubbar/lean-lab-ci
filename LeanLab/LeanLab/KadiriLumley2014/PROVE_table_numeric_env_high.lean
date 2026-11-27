/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 9 Theorem 2.7 display 2.64, page 9
display 3.1 for the weight mass, and Table 2 on page 13. ROUTE BURST S10 burst-20261124,
step tablehighe. This file proves the MEDIUM numeric leaf endpoint_budget_numeric_env_high_S10
of SPLIT_table_endpoint_budget_high_env.lean, step tablehighd, for rows 58, 59, 60 and 150,
under the new name endpoint_budget_numeric_env_high_S10_proved with the identical statement.
Method: the endpoint mass of the polynomial weight is an exact rational, computed by expanding
(4 t (1 - t))^m binomially and integrating term by term, checked by decide +kernel against a
rounded up ratio c per row. The coefficient tailCoefficient is 2 (1 + delta) P L / log P with
P = (e^u - 1) X and L the row index, and log P is bounded below through log 2 < 0.6931471808,
u at least 2^(-34) and log (1 + delta) at most delta. The square root term uses sqrt X at
least s with s^2 at most 2.718^L (1 - u) / (1 + delta). The remaining rational inequality
leaves margins about 0.0217, 0.0196, 0.0217 and 0.0162 in units of (e^u - 1) X.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_table_endpoint_budget_high_env
import LeanLab.KadiriLumley2014.WeightMass

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory Finset
open Task64

/-- Exact integral of the polynomial weight from 0 to a, by the binomial expansion of
(1 - t)^m; the page 9 weight (4 t (1 - t))^m of display 3.1. -/
theorem weight_integral_zero_to_S10e (m : ℕ) (a : ℝ) :
    (∫ t in (0 : ℝ)..a, weight m t) =
      4 ^ m * ∑ k ∈ range (m + 1),
        (-1 : ℝ) ^ k * (m.choose k : ℝ) * (a ^ (m + k + 1) / ((m + k + 1 : ℕ) : ℝ)) := by
  have heq : (fun t : ℝ => weight m t) = fun t => ∑ k ∈ range (m + 1),
      (4 : ℝ) ^ m * ((-1 : ℝ) ^ k * (m.choose k : ℝ) * t ^ (m + k)) := by
    ext t
    rw [← Finset.mul_sum]
    have h1 : weight m t = 4 ^ m * (t ^ m * (-t + 1) ^ m) := by
      unfold weight
      rw [← mul_pow, ← mul_pow]
      ring_nf
    rw [h1, add_pow, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [neg_pow, pow_add]
    ring
  rw [heq, intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
    have h0 : (0 : ℝ) ^ (m + k + 1) = 0 := zero_pow (by omega)
    rw [h0]
    push_cast
    ring
  · intro k _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The normalized endpoint mass tailMass m a over the full mass of display 3.1 is at most c,
given the exact rational inequality, with the binomial coefficient written through
factorials so that the kernel can evaluate it. -/
theorem tail_ratio_le_of_rat_S10e (m : ℕ) (a c : ℚ)
    (h : 2 * (∑ k ∈ range (m + 1), (-1 : ℚ) ^ k *
        ((m.factorial / (k.factorial * (m - k).factorial) : ℕ) : ℚ) *
        (a ^ (m + k + 1) / ((m + k + 1 : ℕ) : ℚ))) * ((2 * m + 1).factorial : ℚ) ≤
      c * (m.factorial : ℚ) ^ 2) :
    tailMass m (a : ℝ) / (∫ t in (0 : ℝ)..1, weight m t) ≤ c := by
  have hR := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hR
  have hsum : ∀ k ∈ range (m + 1),
      (-1 : ℝ) ^ k * (((m.factorial / (k.factorial * (m - k).factorial) : ℕ) : ℝ)) =
      (-1 : ℝ) ^ k * (m.choose k : ℝ) := by
    intro k hk
    rw [Nat.choose_eq_factorial_div_factorial (by simpa [Nat.lt_succ_iff] using hk)]
  rw [div_le_iff₀ (weight_mass_pos m), tailMass_eq_two, weight_integral_zero_to_S10e,
    weight_mass]
  have hp : (2 : ℝ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  rw [hp]
  have hG : (0 : ℝ) < ((2 * m + 1).factorial : ℝ) := by positivity
  rw [show (c : ℝ) * ((4 : ℝ) ^ m * (m.factorial : ℝ) ^ 2 / ((2 * m + 1).factorial : ℝ)) =
      ((4 : ℝ) ^ m * (c * (m.factorial : ℝ) ^ 2)) / ((2 * m + 1).factorial : ℝ) by ring]
  rw [le_div_iff₀ hG]
  have hS : (∑ k ∈ range (m + 1), (-1 : ℝ) ^ k *
        (((m.factorial / (k.factorial * (m - k).factorial) : ℕ) : ℝ)) *
        ((a : ℝ) ^ (m + k + 1) / ((m : ℝ) + k + 1))) =
      ∑ k ∈ range (m + 1),
        (-1 : ℝ) ^ k * (m.choose k : ℝ) * ((a : ℝ) ^ (m + k + 1) / ((m + k + 1 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsum k hk]
    push_cast
    ring
  rw [hS] at hR
  have h4 := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 4 ^ m)
  linarith

/-- Real form of display 2.64 at the row endpoint: with P = (e^u - 1) X, the left side is at
most P times K / (u s) + 2 (1 + delta) L c / ell + 1 / (2 s^4). -/
theorem budget_generic_S10e {δ u X L c B ell s K R : ℝ} (hK : 0 ≤ K) (hu : 0 < u)
    (hδ : 0 ≤ δ) (hs : 0 < s) (hsX : s ^ 2 ≤ X) (hthr : Real.exp u * X * (1 + δ) = Real.exp L)
    (hell : 0 < ell) (hlog : ell ≤ Real.log (X * (Real.exp u - 1))) (hL : 0 ≤ L)
    (hR0 : 0 ≤ R) (hR : R ≤ c)
    (hnum : K / (u * s) + 2 * (1 + δ) * L * c / ell + 1 / (2 * s ^ 4) < 1 + δ / 2 - B) :
    K * Real.sqrt X + tailCoefficient δ u X * R + u / (2 * X) <
      (Real.exp u - 1) * X * (1 + δ / 2 - B) := by
  have hE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hX : 0 < X := lt_of_lt_of_le (by positivity) hsX
  set P := (Real.exp u - 1) * X with hP
  have hPu : u * X ≤ P := mul_le_mul_of_nonneg_right hE hX.le
  have hP0 : 0 < P := lt_of_lt_of_le (mul_pos hu hX) hPu
  have hsq : s ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hsX
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX.le
  have hc0 : 0 ≤ c := hR0.trans hR
  -- term one
  have h1 : K * Real.sqrt X ≤ P * (K / (u * s)) := by
    rw [mul_div_assoc', le_div_iff₀ (mul_pos hu hs)]
    have : u * s * Real.sqrt X ≤ P := by
      have hq : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
      nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hu.le hq)]
    nlinarith [mul_le_mul_of_nonneg_left this hK]
  -- term two
  have htc : tailCoefficient δ u X = P * (2 * (1 + δ) * (L / Real.log (X * (Real.exp u - 1)))) := by
    unfold tailCoefficient
    rw [hthr, Real.log_exp, hP]
    ring
  have hlogpos : 0 < Real.log (X * (Real.exp u - 1)) := lt_of_lt_of_le hell hlog
  have hdiv : L / Real.log (X * (Real.exp u - 1)) ≤ L / ell :=
    div_le_div_of_nonneg_left hL hell hlog
  have hq0 : 0 ≤ L / Real.log (X * (Real.exp u - 1)) := div_nonneg hL hlogpos.le
  have h2 : tailCoefficient δ u X * R ≤ P * (2 * (1 + δ) * L * c / ell) := by
    rw [htc]
    have hA : 2 * (1 + δ) * (L / Real.log (X * (Real.exp u - 1))) * R ≤
        2 * (1 + δ) * (L / ell) * c := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hdiv (by positivity)) hR hR0
      positivity
    have : 2 * (1 + δ) * L * c / ell = 2 * (1 + δ) * (L / ell) * c := by ring
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left hA hP0.le
  -- term three
  have h3 : u / (2 * X) ≤ P * (1 / (2 * s ^ 4)) := by
    rw [div_le_iff₀ (by positivity)]
    have hs4 : s ^ 4 ≤ X * X := by nlinarith [sq_nonneg s]
    have : u * (s ^ 4) ≤ P * X := by
      nlinarith [mul_le_mul_of_nonneg_left hs4 hu.le, mul_le_mul_of_nonneg_right hPu hX.le]
    have hs4p : 0 < s ^ 4 := by positivity
    rw [show P * (1 / (2 * s ^ 4)) * (2 * X) = P * X / s ^ 4 by field_simp]
    rw [le_div_iff₀ hs4p]
    nlinarith
  have hsum := add_le_add (add_le_add h1 h2) h3
  have hlt := mul_lt_mul_of_pos_left hnum hP0
  linarith

/-- Real form of the row facts: from u at least 2^(-34), sqrt X at least s through
2.718^n, and the rational budget, the display 2.64 inequality at X = e^n / (e^u (1 + delta)). -/
theorem budget_from_facts_S10e {δ u X L s c B R K : ℝ} {n : ℕ} (hLn : L = n)
    (hXeq : X = Real.exp L / (Real.exp u * (1 + δ))) (hδ0 : 0 ≤ δ) (hu34 : 1 / 2 ^ 34 ≤ u)
    (hu1 : u < 1) (hs0 : 0 < s) (hsX : s ^ 2 * (1 + δ) ≤ (2718 / 1000) ^ n * (1 - u))
    (hell : 0 < L - u - δ - 34 * (6931471808 / 10 ^ 10)) (hR0 : 0 ≤ R) (hR : R ≤ c)
    (hK : 0 ≤ K)
    (hnum : K / (u * s) + 2 * (1 + δ) * L * c / (L - u - δ - 34 * (6931471808 / 10 ^ 10)) +
        1 / (2 * s ^ 4) < 1 + δ / 2 - B) :
    K * Real.sqrt X + tailCoefficient δ u X * R + u / (2 * X) <
      (Real.exp u - 1) * X * (1 + δ / 2 - B) := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu34
  have hden : 0 < Real.exp u * (1 + δ) := by positivity
  have hthr : Real.exp u * X * (1 + δ) = Real.exp L := by
    rw [hXeq]
    field_simp
  have hX0 : 0 < X := by rw [hXeq]; positivity
  have hE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hlogX : Real.log X = L - u - Real.log (1 + δ) := by
    rw [hXeq, Real.log_div (Real.exp_pos L).ne' hden.ne', Real.log_mul (Real.exp_pos u).ne'
      (by positivity), Real.log_exp, Real.log_exp]
    ring
  have hlog1 : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + δ)
    linarith
  have hlogu : -(34 * Real.log 2) ≤ Real.log u := by
    have h1 : Real.log ((1 : ℝ) / 2 ^ 34) ≤ Real.log u := Real.log_le_log (by positivity) hu34
    rw [one_div, Real.log_inv, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogE : Real.log u ≤ Real.log (Real.exp u - 1) := Real.log_le_log hu0 hE
  have hl2 := Real.log_two_lt_d9
  have hlog : L - u - δ - 34 * (6931471808 / 10 ^ 10) ≤ Real.log (X * (Real.exp u - 1)) := by
    rw [Real.log_mul hX0.ne' (by linarith), hlogX]
    norm_num at hl2 ⊢
    linarith
  have hsX' : s ^ 2 ≤ X := by
    have he1 : Real.exp u ≤ 1 / (1 - u) :=
      Real.exp_bound_div_one_sub_of_interval hu0.le hu1
    have he2 : (2718 / 1000 : ℝ) ^ n ≤ Real.exp L := by
      rw [hLn, ← Real.exp_one_pow]
      apply pow_le_pow_left₀ (by norm_num)
      have := Real.exp_one_gt_d9
      norm_num at this ⊢
      linarith
    have h1u : 0 < 1 - u := by linarith
    have hs2 : (0 : ℝ) ≤ s ^ 2 * (1 + δ) := by positivity
    have h3 : s ^ 2 * (1 + δ) * Real.exp u ≤ s ^ 2 * (1 + δ) * (1 / (1 - u)) :=
      mul_le_mul_of_nonneg_left he1 hs2
    have h2 : s ^ 2 * (1 + δ) * (1 / (1 - u)) ≤ Real.exp L := by
      rw [mul_one_div, div_le_iff₀ h1u]
      nlinarith [mul_le_mul_of_nonneg_right he2 h1u.le]
    have hfin : s ^ 2 * (Real.exp u * (1 + δ)) ≤ X * (Real.exp u * (1 + δ)) := by
      nlinarith
    exact le_of_mul_le_mul_right hfin hden
  exact budget_generic_S10e hK hu0 hδ0 hs0 hsX' hthr hell hlog
    (by rw [hLn]; positivity) hR0 hR hnum

/-- Per row form of the numeric leaf, from rational facts about one row of Table 2 on page 13. -/
theorem numeric_of_row_S10e {r : PrintedRow} (hr : r ∈ tableTwo) (hL0 : r.logIndex ≠ 0)
    (c s bQ : ℚ) (hs0 : 0 < s)
    (hratio : 2 * (∑ k ∈ range (r.m + 1), (-1 : ℚ) ^ k *
        ((r.m.factorial / (k.factorial * (r.m - k).factorial) : ℕ) : ℚ) *
        ((r.aQ + 1 / 10000) ^ (r.m + k + 1) / ((r.m + k + 1 : ℕ) : ℚ))) *
        ((2 * r.m + 1).factorial : ℚ) ≤ c * (r.m.factorial : ℚ) ^ 2)
    (hu34 : 1 / 2 ^ 34 ≤ r.uQ) (hu1 : r.uQ < 1)
    (hsX : s ^ 2 * (1 + r.deltaQ) ≤ (2718 / 1000) ^ r.logIndex * (1 - r.uQ))
    (hell : 0 < (r.logIndex : ℚ) - r.uQ - r.deltaQ - 34 * (6931471808 / 10 ^ 10))
    (hB : highRowEnvelopeBudgetS10 r.logIndex = (bQ : ℝ))
    (hnum : (205022 / 10 ^ 8 : ℚ) / (r.uQ * s) +
        2 * (1 + r.deltaQ) * r.logIndex * c /
          ((r.logIndex : ℚ) - r.uQ - r.deltaQ - 34 * (6931471808 / 10 ^ 10)) +
        1 / (2 * s ^ 4) < 1 + r.deltaQ / 2 - (bQ + 1 / 100000 + 1 / 100000)) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (highRowEnvelopeBudgetS10 r.logIndex + 1 / 100000 + 1 / 100000)) := by
  have hs := table_small_steps r hr
  have hrt := tableTwo_rounding_arithmetic r hr
  have hrat := tail_ratio_le_of_rat_S10e r.m (r.aQ + 1 / 10000) c hratio
  push_cast at hrat
  have hR0 : 0 ≤ tailMass r.m ((r.aQ : ℝ) + 1 / 10000) / (∫ t in (0 : ℝ)..1, weight r.m t) := by
    have ha0 : (0 : ℝ) ≤ (r.aQ : ℝ) + 1 / 10000 := by
      have : (0 : ℝ) ≤ ((r.aQ : ℚ) : ℝ) := by exact_mod_cast hrt.1.2.2.2.1
      linarith
    have ha2 : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hrt.1.2.2.2.2.1
      push_cast at this
      exact this
    exact (tailMass_ratio_bounds r.m ha0 ha2).1
  have hXeq : rowEndpointX r =
      Real.exp (r.logIndex : ℝ) / (Real.exp (r.uQ : ℝ) * (1 + (r.deltaQ : ℝ))) := by
    unfold rowEndpointX PrintedRow.threshold
    rw [if_neg hL0]
  have hKeq : (2.05022 * 10 ^ (-3 : ℤ) : ℝ) = ((205022 / 10 ^ 8 : ℚ) : ℝ) := by norm_num
  rw [mul_div_assoc, hKeq]
  have f1 : (1 : ℝ) / 2 ^ 34 ≤ (r.uQ : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hu34
    push_cast at this
    exact this
  have f2 : (r.uQ : ℝ) < 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hu1
    push_cast at this
    exact this
  have f3 : (s : ℝ) ^ 2 * (1 + (r.deltaQ : ℝ)) ≤
      (2718 / 1000 : ℝ) ^ r.logIndex * (1 - (r.uQ : ℝ)) := by
    have := (Rat.cast_le (K := ℝ)).mpr hsX
    push_cast at this
    exact this
  have f4 : 0 < (r.logIndex : ℝ) - (r.uQ : ℝ) - (r.deltaQ : ℝ) -
      34 * (6931471808 / 10 ^ 10) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hell
    push_cast at this
    exact this
  have f5 : (0 : ℝ) ≤ (r.deltaQ : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hs.1.le
    push_cast at this
    exact this
  have f6 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
  refine budget_from_facts_S10e (δ := (r.deltaQ : ℝ)) (u := (r.uQ : ℝ)) (s := (s : ℝ))
    (c := (c : ℝ)) (L := (r.logIndex : ℝ)) (n := r.logIndex) rfl hXeq
    f5 f1 f2 f6 f3 f4 hR0 hrat (by norm_num) ?_
  rw [hB]
  have h := (Rat.cast_lt (K := ℝ)).mpr hnum
  push_cast at h ⊢
  linarith

/-- PROVED form of the MEDIUM leaf endpoint_budget_numeric_env_high_S10 of step tablehighd,
page 9 display 2.64 at the row endpoint for rows 58, 59, 60 and 150 of Table 2 on page 13,
with the identical statement. -/
theorem endpoint_budget_numeric_env_high_S10_proved {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (highRowEnvelopeBudgetS10 r.logIndex + 1 / 100000 + 1 / 100000)) := by
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at hhigh <;> try omega
  · exact numeric_of_row_S10e (by simp [tableTwo]) (by decide) (27992 / 100000) (3 * 10 ^ 12)
      (3530 / 100000) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by simp [highRowEnvelopeBudgetS10]; norm_num) (by decide +kernel)
  · exact numeric_of_row_S10e (by simp [tableTwo]) (by decide) (28796 / 100000) (6 * 10 ^ 12)
      (2142 / 100000) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by simp [highRowEnvelopeBudgetS10]; norm_num) (by decide +kernel)
  · exact numeric_of_row_S10e (by simp [tableTwo]) (by decide) (29307 / 100000) (10 ^ 13)
      (1300 / 100000) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by simp [highRowEnvelopeBudgetS10]; norm_num) (by decide +kernel)
  · exact numeric_of_row_S10e (by simp [tableTwo]) (by decide) (41459 / 100000) (10 ^ 30)
      (2 / 100000) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by simp [highRowEnvelopeBudgetS10]; norm_num) (by decide +kernel)

/-- Assembly: the exact statement of table_endpoint_budget_high, now resting only on the HARD
envelope leaf endpoint_low_height_envelope_high_S10 and the leaves of steps tablehighb and
tablehighc, with the proof of step tablehighd repeated and its numeric leaf replaced by the
proved form above. CONDITIONAL ON those leaves. -/
theorem table_endpoint_budget_high_numeric_closed_S10e {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  have hL0 : 0 ≤ highRowEnvelopeBudgetS10 r.logIndex := by
    simpa using endpoint_low_height_envelope_high_S10 hr hhigh ∅
  have hZ : zeroError r.m r.deltaQ r.uQ (rowEndpointX r) ≤
      highRowEnvelopeBudgetS10 r.logIndex + 1 / 100000 + 1 / 100000 := by
    unfold zeroError
    refine tsum_le_of_sum_le' (by linarith) (fun s => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.1.im| ≤ 30610000000)]
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000))
      (fun ρ => |ρ.1.im| ≤ 3000000000000)]
    rw [Finset.filter_filter]
    have h1 := endpoint_low_height_envelope_high_S10 hr hhigh s
    have h2 := endpoint_mid_height_zero_sum_high_split_S10 hr hhigh s
    have h3 := endpoint_top_height_zero_tail_high_split_S10 hr hhigh
      (s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000))
    linarith
  have hs := table_small_steps r hr
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX
    have := Real.exp_pos (r.uQ : ℝ)
    have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
    have hth : 0 < r.threshold := by
      unfold PrintedRow.threshold
      split_ifs
      · norm_num [evenBase]
      · exact Real.exp_pos _
    positivity
  have hE : 0 < Real.exp (r.uQ : ℝ) - 1 := by
    have := Real.add_one_lt_exp hu.ne'
    linarith
  have hP : 0 < (Real.exp r.uQ - 1) * rowEndpointX r := mul_pos hE hX
  refine (endpoint_budget_numeric_env_high_S10_proved hr hhigh).trans_le ?_
  apply mul_le_mul_of_nonneg_left _ hP.le
  linarith


#print axioms weight_integral_zero_to_S10e
#print axioms tail_ratio_le_of_rat_S10e
#print axioms budget_generic_S10e
#print axioms budget_from_facts_S10e
#print axioms numeric_of_row_S10e
#print axioms endpoint_budget_numeric_env_high_S10_proved
#print axioms table_endpoint_budget_high_numeric_closed_S10e

end LeanLab.KadiriLumley2014.Task92
