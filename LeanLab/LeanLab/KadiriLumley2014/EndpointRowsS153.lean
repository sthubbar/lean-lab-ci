/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 9 display 2.64 and page 13 Table 2.
Burst S153 burst-20261122: exact tools for the per row LEAFs of SPLIT_endpoint_budget_numeric.
The weight (4t(1-t))^m of page 9 integrates to the explicit polynomial rowWPrim, so nu over the
weight mass is an exact rational per row, checked by decide +kernel. The row inequality then
reduces to rational bounds for log of the threshold and of X(e^u - 1).
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_table_endpoint_budget_low

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- The antiderivative of the page 9 weight (4t(1-t))^m at a, as an exact rational:
the sum over k of choose m k (-1)^k 4^m a^(m+k+1)/(m+k+1). Helper definition for the
per row numerics of page 13 Table 2, reviewer please check. -/
def rowWPrim (m : ℕ) (a : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), (m.choose k : ℚ) * (-1) ^ k * 4 ^ m * a ^ (m + k + 1) / (m + k + 1)

theorem weight_expand_S153 (m : ℕ) (t : ℝ) :
    Task64.weight m t = ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (-1) ^ k * 4 ^ m * t ^ (m + k) := by
  have h : (1 - t) ^ m = ∑ k ∈ Finset.range (m + 1), (-t) ^ k * 1 ^ (m - k) * (m.choose k : ℝ) := by
    rw [← add_pow]; ring
  rw [Task64.weight, mul_pow, mul_pow, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_pow, pow_add]; ring

theorem integral_weight_eq_rowWPrim (m : ℕ) (a : ℚ) :
    ∫ t in (0:ℝ)..(a:ℝ), Task64.weight m t = ((rowWPrim m a : ℚ) : ℝ) := by
  simp_rw [weight_expand_S153]
  rw [intervalIntegral.integral_finsetSum]
  · unfold rowWPrim
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have : (m : ℝ) + k + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · intro k _
    exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _

theorem rowWPrim_one_pos_5 : 0 < rowWPrim 5 1 := by decide +kernel
theorem rowWPrim_one_pos_6 : 0 < rowWPrim 6 1 := by decide +kernel
theorem rowWPrim_one_pos_7 : 0 < rowWPrim 7 1 := by decide +kernel
theorem rowWPrim_one_pos_8 : 0 < rowWPrim 8 1 := by decide +kernel
theorem rowWPrim_one_pos_9 : 0 < rowWPrim 9 1 := by decide +kernel
theorem rowWPrim_one_pos_11 : 0 < rowWPrim 11 1 := by decide +kernel
theorem rowWPrim_one_pos_15 : 0 < rowWPrim 15 1 := by decide +kernel
theorem rowWPrim_one_pos_20 : 0 < rowWPrim 20 1 := by decide +kernel
theorem rowWPrim_one_pos_28 : 0 < rowWPrim 28 1 := by decide +kernel
theorem rowWPrim_one_pos_39 : 0 < rowWPrim 39 1 := by decide +kernel
theorem rowWPrim_one_pos_48 : 0 < rowWPrim 48 1 := by decide +kernel
theorem rowWPrim_one_pos_54 : 0 < rowWPrim 54 1 := by decide +kernel
theorem rowWPrim_one_pos_56 : 0 < rowWPrim 56 1 := by decide +kernel
theorem rowWPrim_one_pos_59 : 0 < rowWPrim 59 1 := by decide +kernel

/-- c = 0.031834, exact ratio about 0.0318335057 -/
theorem row_nu_ratio_5_2129 : 2 * rowWPrim 5 (2130/10000) / rowWPrim 5 1 ≤ 15917/500000 := by decide +kernel
/-- c = 0.033175, exact ratio about 0.0331748761 -/
theorem row_nu_ratio_5_2147 : 2 * rowWPrim 5 (2148/10000) / rowWPrim 5 1 ≤ 1327/40000 := by decide +kernel
/-- c = 0.032730, exact ratio about 0.0327297754 -/
theorem row_nu_ratio_6_2324 : 2 * rowWPrim 6 (2325/10000) / rowWPrim 6 1 ≤ 3273/100000 := by decide +kernel
/-- c = 0.034183, exact ratio about 0.0341822117 -/
theorem row_nu_ratio_7_2494 : 2 * rowWPrim 7 (2495/10000) / rowWPrim 7 1 ≤ 34183/1000000 := by decide +kernel
/-- c = 0.036702, exact ratio about 0.0367018622 -/
theorem row_nu_ratio_8_2651 : 2 * rowWPrim 8 (2652/10000) / rowWPrim 8 1 ≤ 18351/500000 := by decide +kernel
/-- c = 0.044342, exact ratio about 0.0443415839 -/
theorem row_nu_ratio_9_2836 : 2 * rowWPrim 9 (2837/10000) / rowWPrim 9 1 ≤ 22171/500000 := by decide +kernel
/-- c = 0.049011, exact ratio about 0.0490100390 -/
theorem row_nu_ratio_11_3050 : 2 * rowWPrim 11 (3051/10000) / rowWPrim 11 1 ≤ 49011/1000000 := by decide +kernel
/-- c = 0.045823, exact ratio about 0.0458225341 -/
theorem row_nu_ratio_15_3275 : 2 * rowWPrim 15 (3276/10000) / rowWPrim 15 1 ≤ 45823/1000000 := by decide +kernel
/-- c = 0.055139, exact ratio about 0.0551381545 -/
theorem row_nu_ratio_20_3543 : 2 * rowWPrim 20 (3544/10000) / rowWPrim 20 1 ≤ 55139/1000000 := by decide +kernel
/-- c = 0.077081, exact ratio about 0.0770809342 -/
theorem row_nu_ratio_28_3849 : 2 * rowWPrim 28 (3850/10000) / rowWPrim 28 1 ≤ 77081/1000000 := by decide +kernel
/-- c = 0.117104, exact ratio about 0.1171030584 -/
theorem row_nu_ratio_39_4127 : 2 * rowWPrim 39 (4128/10000) / rowWPrim 39 1 ≤ 7319/62500 := by decide +kernel
/-- c = 0.165979, exact ratio about 0.1659784414 -/
theorem row_nu_ratio_48_4301 : 2 * rowWPrim 48 (4302/10000) / rowWPrim 48 1 ≤ 165979/1000000 := by decide +kernel
/-- c = 0.206809, exact ratio about 0.2068088518 -/
theorem row_nu_ratio_54_4398 : 2 * rowWPrim 54 (4399/10000) / rowWPrim 54 1 ≤ 206809/1000000 := by decide +kernel
/-- c = 0.236382, exact ratio about 0.2363819086 -/
theorem row_nu_ratio_56_4445 : 2 * rowWPrim 56 (4446/10000) / rowWPrim 56 1 ≤ 118191/500000 := by decide +kernel
/-- c = 0.256134, exact ratio about 0.2561332019 -/
theorem row_nu_ratio_59_4481 : 2 * rowWPrim 59 (4482/10000) / rowWPrim 59 1 ≤ 128067/500000 := by decide +kernel
/-- c = 0.270234, exact ratio about 0.2702339106 -/
theorem row_nu_ratio_59_4496 : 2 * rowWPrim 59 (4497/10000) / rowWPrim 59 1 ≤ 135117/500000 := by decide +kernel


/-- An upper bound for log y from y^k at most 2.7182818283^n, below e^n. -/
theorem log_le_of_pow_le_S153 {y : ℝ} (_hy : 0 < y) {n k : ℕ} (hk : 0 < k)
    (h : y ^ k ≤ (2.7182818283 : ℝ) ^ n) : Real.log y ≤ (n : ℝ) / k := by
  have he : (2.7182818283 : ℝ) ^ n ≤ Real.exp n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n
  have h2 : Real.log (y ^ k) ≤ n := by
    rw [← Real.log_exp (n : ℝ)]
    exact Real.log_le_log (by positivity) (h.trans he)
  rw [Real.log_pow] at h2
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hk']; linarith

/-- A lower bound for log y from 2.7182818286^n at most y^k, above e^n. -/
theorem le_log_of_le_pow_S153 {y : ℝ} (_hy : 0 < y) {n k : ℕ} (hk : 0 < k)
    (h : (2.7182818286 : ℝ) ^ n ≤ y ^ k) : (n : ℝ) / k ≤ Real.log y := by
  have he : Real.exp n ≤ (2.7182818286 : ℝ) ^ n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n
  have h2 : (n : ℝ) ≤ Real.log (y ^ k) := by
    rw [← Real.log_exp (n : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) (he.trans h)
  rw [Real.log_pow] at h2
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hk']; linarith

/-- Page 9 display 2.64 at a row endpoint, reduced to rational data: with nu at most q times
the weight mass, log T at most LT, log T at least LTlo, (1+δ)(1+u)/u at most Y with log Y at
most KY, and 4 s0^2 at most T, the display holds once the displayed rational inequality holds. -/
theorem row_closer_S153 {δ u T X ν I q LT LTlo Y KY s0 B c0 : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1 / 2) (hX : X = T / (Real.exp u * (1 + δ)))
    (hT1 : 1 ≤ T) (hI : 0 < I) (hν : ν ≤ q * I) (hq : 0 ≤ q)
    (hLT : Real.log T ≤ LT) (hLTlo : LTlo ≤ Real.log T)
    (hY : (1 + δ) * (1 + u) / u ≤ Y) (hKY : Real.log Y ≤ KY) (hL : 0 < LTlo - KY)
    (hs0 : 0 < s0) (hsT : 4 * s0 ^ 2 ≤ T) (hc0 : 0 ≤ c0)
    (hfin : c0 / (u * s0) + 2 * (1 + δ) * (LT / (LTlo - KY)) * q + 1 / (2 * s0 ^ 4) <
      1 + δ / 2 - B) :
    c0 * Real.sqrt X + tailCoefficient δ u X * ν / I + u / (2 * X) <
      (Real.exp u - 1) * X * (1 + δ / 2 - B) := by
  have hT0 : 0 < T := by linarith
  have heu : 0 < Real.exp u := Real.exp_pos u
  have hE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hE0 : 0 < Real.exp u - 1 := by linarith
  have heu2 : Real.exp u ≤ 2 := by
    have := Real.exp_bound' (x := u) hu.le (by linarith) (n := 1) (by norm_num)
    simp at this
    nlinarith
  have hX0 : 0 < X := by rw [hX]; positivity
  -- X is at least s0^2
  have hXs : s0 ^ 2 ≤ X := by
    rw [hX, le_div_iff₀ (by positivity)]
    have h4 : Real.exp u * (1 + δ) ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg s0)]
  have hsq : s0 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hXs
  have hsqpos : 0 < Real.sqrt X := lt_of_lt_of_le hs0 hsq
  set E := Real.exp u - 1 with hEdef
  set Q := E * X with hQ
  have hQ0 : 0 < Q := by positivity
  -- term 1
  have hXX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have h1 : c0 * Real.sqrt X ≤ Q * (c0 / (u * s0)) := by
    have hge : 1 ≤ E * Real.sqrt X / (u * s0) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact mul_le_mul hE hsq hs0.le hE0.le
    calc c0 * Real.sqrt X = c0 * Real.sqrt X * 1 := by ring
      _ ≤ c0 * Real.sqrt X * (E * Real.sqrt X / (u * s0)) :=
          mul_le_mul_of_nonneg_left hge (by positivity)
      _ = Q * (c0 / (u * s0)) := by
          rw [hQ, div_eq_mul_inv, div_eq_mul_inv]
          linear_combination (c0 * E * (u * s0)⁻¹) * hXX
  -- term 3
  have h3 : u / (2 * X) ≤ Q * (1 / (2 * s0 ^ 4)) := by
    rw [hQ, div_le_iff₀ (by positivity)]
    have hX2 : s0 ^ 4 ≤ X * X := by nlinarith
    have : u * (2 * s0 ^ 4) ≤ E * X * (1 / (2 * s0 ^ 4)) * (2 * X) * (2 * s0 ^ 4) := by
      field_simp
      nlinarith [mul_le_mul hE hX2 (by positivity) hE0.le]
    nlinarith [this, (by positivity : (0:ℝ) < 2 * s0 ^ 4)]
  -- term 2
  have hTe : Real.exp u * X * (1 + δ) = T := by rw [hX]; field_simp
  have hXE : T / Y ≤ X * E := by
    have hfrac : u / (1 + u) ≤ E / Real.exp u := by
      rw [div_le_div_iff₀ (by linarith) heu, hEdef]
      have := Real.add_one_le_exp u
      ring_nf; linarith
    have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY
    have hXE' : X * E = T * (E / Real.exp u) / (1 + δ) := by rw [hX]; field_simp
    rw [hXE', div_le_div_iff₀ hY0 (by linarith)]
    have : T * (1 + δ) ≤ T * (E / Real.exp u) * Y := by
      have hYu : (1 + δ) ≤ u / (1 + u) * Y := by
        rw [div_le_iff₀ hu] at hY
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        linarith
      calc T * (1 + δ) ≤ T * (u / (1 + u) * Y) := mul_le_mul_of_nonneg_left hYu hT0.le
        _ ≤ T * (E / Real.exp u * Y) := by
          apply mul_le_mul_of_nonneg_left _ hT0.le
          exact mul_le_mul_of_nonneg_right hfrac (le_trans (by positivity) hY)
        _ = _ := by ring
    linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY
  have hlogXE : LTlo - KY ≤ Real.log (X * E) := by
    have := Real.log_le_log (by positivity) hXE
    rw [Real.log_div hT0.ne' hY0.ne'] at this
    linarith
  have hlogXE0 : 0 < Real.log (X * E) := lt_of_lt_of_le hL hlogXE
  have hLT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hratio : Real.log T / Real.log (X * E) ≤ LT / (LTlo - KY) := by
    calc Real.log T / Real.log (X * E) ≤ LT / Real.log (X * E) :=
          div_le_div_of_nonneg_right hLT hlogXE0.le
      _ ≤ LT / (LTlo - KY) := div_le_div_of_nonneg_left (hLT0.trans hLT) hL hlogXE
  have hνI : ν / I ≤ q := by rw [div_le_iff₀ hI]; linarith
  have hν0 : True := trivial
  have h2 : tailCoefficient δ u X * ν / I ≤ Q * (2 * (1 + δ) * (LT / (LTlo - KY)) * q) := by
    unfold tailCoefficient
    rw [hTe]
    have hrr : 0 ≤ Real.log T / Real.log (X * E) := div_nonneg hLT0 hlogXE0.le
    have e1 : 2 * (1 + δ) * E * (Real.log T / Real.log (X * E)) * X * ν / I =
        Q * (2 * (1 + δ)) * ((Real.log T / Real.log (X * E)) * (ν / I)) := by
      rw [hQ]; ring
    rw [e1, show Q * (2 * (1 + δ) * (LT / (LTlo - KY)) * q) =
        Q * (2 * (1 + δ)) * ((LT / (LTlo - KY)) * q) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rcases le_or_gt 0 (ν / I) with hn | hn
    · exact mul_le_mul hratio hνI hn (le_trans hrr hratio)
    · have : Real.log T / Real.log (X * E) * (ν / I) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hrr hn.le
      exact this.trans (mul_nonneg (le_trans hrr hratio) hq)
  have hsum := add_le_add (add_le_add h1 h2) h3
  have hfin' := mul_lt_mul_of_pos_left hfin hQ0
  calc c0 * Real.sqrt X + tailCoefficient δ u X * ν / I + u / (2 * X) ≤
      Q * (c0 / (u * s0)) + Q * (2 * (1 + δ) * (LT / (LTlo - KY)) * q) +
        Q * (1 / (2 * s0 ^ 4)) := hsum
    _ = Q * (c0 / (u * s0) + 2 * (1 + δ) * (LT / (LTlo - KY)) * q + 1 / (2 * s0 ^ 4)) := by ring
    _ < Q * (1 + δ / 2 - B) := hfin'
    _ = _ := by rw [hQ]

/-- exp n is at least 2.7182818283^n. -/
theorem exp_nat_ge_S153 (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n

/-- log_le_of_pow_le_S153 with the power check done in ℚ, for decide +kernel. -/
theorem log_le_of_pow_le_rat_S153 {y : ℚ} (hy : 0 < y) {n k : ℕ} (hk : 0 < k)
    (h : y ^ k ≤ (27182818283 / 10000000000 : ℚ) ^ n) : Real.log (y : ℝ) ≤ (n : ℝ) / k := by
  refine log_le_of_pow_le_S153 (by exact_mod_cast hy) hk ?_
  have h' : (((y ^ k : ℚ)) : ℝ) ≤ (((27182818283 / 10000000000 : ℚ) ^ n : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  norm_num at h' ⊢
  exact h'

/-- le_log_of_le_pow_S153 with the power check done in ℚ, for decide +kernel. -/
theorem le_log_of_le_pow_rat_S153 {y : ℚ} (hy : 0 < y) {n k : ℕ} (hk : 0 < k)
    (h : (27182818286 / 10000000000 : ℚ) ^ n ≤ y ^ k) : (n : ℝ) / k ≤ Real.log (y : ℝ) := by
  refine le_log_of_le_pow_S153 (by exact_mod_cast hy) hk ?_
  have h' : (((27182818286 / 10000000000 : ℚ) ^ n : ℚ) : ℝ) ≤ (((y ^ k : ℚ)) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  norm_num at h' ⊢
  exact h'

end LeanLab.KadiriLumley2014.Task92
