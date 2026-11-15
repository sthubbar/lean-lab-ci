/-
Jia 1996 pages 261 and 262, the finite base checks in Lemma 20.
Source https://doi.org/10.4064/aa-77-3-207-287.
Only two finite grid statements remain OPEN in this numerical input.
Interpolation and propagation use the actual constructed Buchstab function.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Bounds578
import LeanLab.Languasco2004.Endpoints578

namespace LeanLab.Languasco2004.Decomp578e
open Real Finset intervalIntegral Buchstab578 Bounds578 Geometry565
noncomputable section


section
open LogApprox565
set_option maxHeartbeats 0


/-! ## Certified rational bounds for logarithms -/

private theorem log_rat_bounds (x lo hi : ℝ) (h0 : 0 ≤ x) (h1 : x < 1)
    (hl : lo ≤ 2 * ∑ i ∈ range 12, x ^ (2 * i + 1) / (2 * i + 1))
    (hh : 2 * ((∑ i ∈ range 12, x ^ (2 * i + 1) / (2 * i + 1)) +
      x ^ (2 * 12 + 1) / (1 - x ^ 2)) ≤ hi) :
    lo ≤ log ((1 + x) / (1 - x)) ∧ log ((1 + x) / (1 - x)) ≤ hi := by
  have h1' := Real.sum_range_le_log_div h0 h1 12
  have h2' := Real.log_div_le_sum_range_add h0 h1 12
  constructor <;> linarith

private theorem log_two_four_six :
    (0.9001613 : ℝ) ≤ log 2.46 ∧ log 2.46 ≤ 0.9001614 := by
  have h := log_rat_bounds (73 / 173) 0.9001613 0.9001614 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 73 / 173) / (1 - 73 / 173) = (2.46 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_two_four_seven :
    (0.9042181 : ℝ) ≤ log 2.47 ∧ log 2.47 ≤ 0.9042182 := by
  have h := log_rat_bounds (147 / 347) 0.9042181 0.9042182 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 147 / 347) / (1 - 147 / 347) = (2.47 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_one_four_six :
    (0.3784364 : ℝ) ≤ log 1.46 ∧ log 1.46 ≤ 0.3784365 := by
  have h := log_rat_bounds (23 / 123) 0.3784364 0.3784365 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 23 / 123) / (1 - 23 / 123) = (1.46 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_one_four_seven :
    (0.3852624 : ℝ) ≤ log 1.47 ∧ log 1.47 ≤ 0.3852625 := by
  have h := log_rat_bounds (47 / 247) 0.3852624 0.3852625 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 47 / 247) / (1 - 47 / 247) = (1.47 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_one_five :
    (0.4054651 : ℝ) ≤ log 1.5 ∧ log 1.5 ≤ 0.4054652 := by
  have h := log_rat_bounds (1 / 5) 0.4054651 0.4054652 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 1 / 5) / (1 - 1 / 5) = (1.5 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_one_six :
    (0.4700036 : ℝ) ≤ log 1.6 ∧ log 1.6 ≤ 0.4700037 := by
  have h := log_rat_bounds (3 / 13) 0.4700036 0.4700037 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 3 / 13) / (1 - 3 / 13) = (1.6 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_one_seven_five :
    (0.5596157 : ℝ) ≤ log 1.75 ∧ log 1.75 ≤ 0.5596158 := by
  have h := log_rat_bounds (3 / 11) 0.5596157 0.5596158 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 3 / 11) / (1 - 3 / 11) = (1.75 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_one_eight :
    (0.5877866 : ℝ) ≤ log 1.8 ∧ log 1.8 ≤ 0.5877867 := by
  have h := log_rat_bounds (2 / 7) 0.5877866 0.5877867 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 2 / 7) / (1 - 2 / 7) = (1.8 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_two_five :
    (0.9162907 : ℝ) ≤ log 2.5 ∧ log 2.5 ≤ 0.9162908 := by
  have h := log_rat_bounds (3 / 7) 0.9162907 0.9162908 (by norm_num) (by norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
    (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  have he : (1 + 3 / 7) / (1 - 3 / 7) = (2.5 : ℝ) := by norm_num
  rwa [he] at h

private theorem log_three :
    (1.0986122 : ℝ) ≤ log 3 ∧ log 3 ≤ 1.0986124 := by
  have h : log 3 = log 2 + log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  have h32 := LogApprox565.log_three_halves_bounds
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, h32.1, h32.2, h]

/-! ## Linear comparison bounds for the logarithm -/

private theorem log_ge_linear (c₀ y Y : ℝ) (h0 : 0 < c₀) (h1 : c₀ ≤ y) (h2 : y ≤ Y) :
    log c₀ + (y - c₀) * (1 / Y) ≤ log y := by
  have hy : 0 < y := lt_of_lt_of_le h0 h1
  have hY : 0 < Y := lt_of_lt_of_le h0 (h1.trans h2)
  have hq : 0 < y / c₀ := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hq
  have hinv : (y / c₀)⁻¹ = c₀ / y := by field_simp
  rw [hinv] at h
  have hlog : log y = log c₀ + log (y / c₀) := by
    rw [Real.log_div hy.ne' h0.ne']
    ring
  have hval : (1 : ℝ) - c₀ / y = (y - c₀) * (1 / y) := by
    rw [mul_one_div, sub_div, div_self hy.ne']
  rw [hval] at h
  have hmono : (y - c₀) * (1 / Y) ≤ (y - c₀) * (1 / y) := by
    have hY' : 0 < Y := lt_of_lt_of_le h0 (h1.trans h2)
    have : (1 : ℝ) / Y ≤ 1 / y := one_div_le_one_div_of_le hy h2
    exact mul_le_mul_of_nonneg_left this (by linarith)
  linarith

private theorem log_le_tangent (c₀ y : ℝ) (h0 : 0 < c₀) (h1 : 0 < y) :
    log y ≤ log c₀ + (y - c₀) * (1 / c₀) := by
  have h := Real.log_le_sub_one_of_pos (show 0 < y / c₀ by positivity)
  have hlog : log y = log c₀ + log (y / c₀) := by
    rw [Real.log_div h1.ne' h0.ne']
    ring
  have hval : y / c₀ - 1 = (y - c₀) * (1 / c₀) := by
    rw [mul_one_div, sub_div, div_self h0.ne']
  rw [hval] at h
  linarith

private theorem log_le_linear (c₀ y : ℝ) (h0 : 0 < c₀) (h1 : c₀ ≤ y) :
    log y ≤ log c₀ + (y - c₀) * (1 / c₀) :=
  log_le_tangent c₀ y h0 (lt_of_lt_of_le h0 h1)

/-! ## The truncated polynomial integrals -/

private theorem poly_int_two_four_six :
    (0.0402879 : ℝ) ≤ ∫ t in (2 : ℝ)..(2.46), logPoly (-1 + 1 * t) * recipPoly 2.46 t ∧
      (∫ t in (2 : ℝ)..(2.46), logPoly (-1 + 1 * t) * recipPoly 2.46 t) ≤ 0.0402881 := by
  constructor
  · unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  · unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num

private theorem poly_int_two_four_seven :
    (0.0418370 : ℝ) ≤ ∫ t in (2 : ℝ)..(2.47), logPoly (-1 + 1 * t) * recipPoly 2.47 t ∧
      (∫ t in (2 : ℝ)..(2.47), logPoly (-1 + 1 * t) * recipPoly 2.47 t) ≤ 0.0418372 := by
  constructor
  · unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  · unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num

private theorem poly_int_two_five :
    (0.0466102 : ℝ) ≤ ∫ t in (2 : ℝ)..(2.5), logPoly (-1 + 1 * t) * recipPoly 2.5 t ∧
      (∫ t in (2 : ℝ)..(2.5), logPoly (-1 + 1 * t) * recipPoly 2.5 t) ≤ 0.0466104 := by
  constructor
  · unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  · unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num

/-! ## Bounds for the logarithmic integral -/

private theorem J_of_poly (a b lo hi : ℝ) (hab : a ≤ b) (ha : 1 / 10 ≤ a)
    (hab' : 3 / 5 * b ≤ a) (hb : 0 < b) (hb3 : b ≤ 3)
    (hy : ∀ t ∈ Set.Icc a b, 1 ≤ -1 + 1 * t ∧ -1 + 1 * t ≤ 2)
    (hp : lo ≤ ∫ t in a..b, logPoly (-1 + 1 * t) * recipPoly b t)
    (hp2 : (∫ t in a..b, logPoly (-1 + 1 * t) * recipPoly b t) ≤ hi) :
    lo - 0.0000001 ≤ ∫ t in a..b, log (t - 1) / t ∧
      (∫ t in a..b, log (t - 1) / t) ≤ hi + 0.0000001 := by
  have happ := integral_log_approx a b (-1) 1 hab ha hab' hb hy
  have heq : (∫ t in a..b, log (-1 + 1 * t) / t) = ∫ t in a..b, log (t - 1) / t := by
    apply integral_congr
    intro t _
    congr 1
    ring
  rw [heq] at happ
  obtain ⟨h1, h2⟩ := abs_le.mp happ
  have hba : 2e-8 * (b - a) ≤ 0.0000001 := by nlinarith
  constructor <;> linarith

private theorem J_two_four_six :
    (0.0402868 : ℝ) ≤ ∫ t in (2 : ℝ)..(2.46), log (t - 1) / t ∧
      (∫ t in (2 : ℝ)..(2.46), log (t - 1) / t) ≤ 0.0402892 := by
  obtain ⟨hp, hp2⟩ := poly_int_two_four_six
  obtain ⟨h1, h2⟩ := J_of_poly 2 2.46 0.0402879 0.0402881 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by intro t ht; constructor <;> linarith [ht.1, ht.2]) hp hp2
  constructor <;> linarith

private theorem J_two_four_seven :
    (0.0418359 : ℝ) ≤ ∫ t in (2 : ℝ)..(2.47), log (t - 1) / t ∧
      (∫ t in (2 : ℝ)..(2.47), log (t - 1) / t) ≤ 0.0418383 := by
  obtain ⟨hp, hp2⟩ := poly_int_two_four_seven
  obtain ⟨h1, h2⟩ := J_of_poly 2 2.47 0.0418370 0.0418372 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by intro t ht; constructor <;> linarith [ht.1, ht.2]) hp hp2
  constructor <;> linarith

private theorem J_two_five :
    (0.0465 : ℝ) ≤ ∫ t in (2 : ℝ)..(2.5), log (t - 1) / t ∧
      (∫ t in (2 : ℝ)..(2.5), log (t - 1) / t) ≤ 0.0467 := by
  obtain ⟨hp, hp2⟩ := poly_int_two_five
  obtain ⟨h1, h2⟩ := J_of_poly 2 2.5 0.0466102 0.0466104 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by intro t ht; constructor <;> linarith [ht.1, ht.2]) hp hp2
  constructor <;> linarith

/-! ## The comparison functions -/

private theorem Phi_sub_Phi (c a b : ℝ) (h2 : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    ((∫ t in (2 : ℝ)..b, log (t - 1) / t) - (c * (b + 1) - 1 - log b)) -
      ((∫ t in (2 : ℝ)..a, log (t - 1) / t) - (c * (a + 1) - 1 - log a)) =
      ∫ t in a..b, (log (t - 1) - c * t + 1) / t := by
  have hc : ContinuousOn (fun t : ℝ => log (t - 1) / t) (Set.Icc (2 : ℝ) 3) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro t ht
      linarith [ht.1]
    · fun_prop
    · intro t ht
      linarith [ht.1]
  have hi1 : IntervalIntegrable (fun t : ℝ => log (t - 1) / t) MeasureTheory.volume 2 a :=
    ContinuousOn.intervalIntegrable_of_Icc h2
      (hc.mono (by intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩))
  have hi2 : IntervalIntegrable (fun t : ℝ => log (t - 1) / t) MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (hc.mono (by intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hiG : IntervalIntegrable (fun t : ℝ => 1 / t) MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (by
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le (by linarith : (0:ℝ) < a) ht.1))
  have hC : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b := continuous_const.intervalIntegrable a b
  have hinv : (∫ t in a..b, 1 / t) = log b - log a := by
    rw [integral_one_div_of_pos (by linarith) (by linarith),
      Real.log_div (by linarith : b ≠ 0) (by linarith : a ≠ 0)]
  have hcongr : (∫ t in a..b, (log (t - 1) - c * t + 1) / t) =
      ∫ t in a..b, (log (t - 1) / t - c + 1 / t) := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by linarith : (0:ℝ) < a) ht.1
    change (log (t - 1) - c * t + 1) / t = log (t - 1) / t - c + 1 / t
    rw [add_div, sub_div, mul_div_cancel_right₀ c ht0.ne']
  have e1 : (∫ t in a..b, (log (t - 1) / t - c + 1 / t))
      = (∫ t in a..b, log (t - 1) / t) - (∫ t in a..b, (fun _ : ℝ => c) t) +
        (∫ t in a..b, 1 / t) := by
    rw [intervalIntegral.integral_add (hi2.sub hC) hiG, intervalIntegral.integral_sub hi2 hC]
  have e2 : (∫ t in a..b, (fun _ : ℝ => c) t) = c * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hcongr, e1, e2, hinv]
  linarith [hadd]

private theorem Phi_le_of_nonneg (c a b : ℝ) (h2 : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (hsgn : ∀ t ∈ Set.Icc a b, 0 ≤ log (t - 1) - c * t + 1) :
    (∫ t in (2 : ℝ)..a, log (t - 1) / t) - (c * (a + 1) - 1 - log a) ≤
      (∫ t in (2 : ℝ)..b, log (t - 1) / t) - (c * (b + 1) - 1 - log b) := by
  have h := Phi_sub_Phi c a b h2 hab hb
  have hnn : 0 ≤ ∫ t in a..b, (log (t - 1) - c * t + 1) / t := by
    apply integral_nonneg hab
    intro t ht
    change 0 ≤ (log (t - 1) - c * t + 1) / t
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by linarith : (0:ℝ) < a) ht.1
    have hs := hsgn t ht
    rw [div_eq_mul_inv]
    exact mul_nonneg hs (le_of_lt (by positivity))
  linarith

private theorem Phi_le_of_nonpos (c a b : ℝ) (h2 : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (hsgn : ∀ t ∈ Set.Icc a b, log (t - 1) - c * t + 1 ≤ 0) :
    (∫ t in (2 : ℝ)..b, log (t - 1) / t) - (c * (b + 1) - 1 - log b) ≤
      (∫ t in (2 : ℝ)..a, log (t - 1) / t) - (c * (a + 1) - 1 - log a) := by
  have h := Phi_sub_Phi c a b h2 hab hb
  have hneg : 0 ≤ ∫ t in a..b, -((log (t - 1) - c * t + 1) / t) := by
    apply integral_nonneg hab
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by linarith : (0:ℝ) < a) ht.1
    have hs := hsgn t ht
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hs ht0.le)
  have heqneg : (∫ t in a..b, -((log (t - 1) - c * t + 1) / t)) =
      -(∫ t in a..b, (log (t - 1) - c * t + 1) / t) := by
    have e2 : (fun t : ℝ => -((log (t - 1) - c * t + 1) / t)) =
        fun t : ℝ => -(fun s : ℝ => (log (s - 1) - c * s + 1) / s) t := rfl
    rw [e2, intervalIntegral.integral_neg]
  rw [heqneg] at hneg
  linarith

/-! ## Sign of the comparison derivative on two to three -/

private theorem q_lower_neg (s : ℝ) (h2 : 2 ≤ s) (h3 : s ≤ 2.46) :
    log (s - 1) - 0.56081 * s + 1 ≤ 0 := by
  have hs : 0 < s - 1 := by linarith
  have hq : 0 < 1.46 / (s - 1) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hq
  have hinv : (1.46 / (s - 1))⁻¹ = (s - 1) / 1.46 := by rw [inv_div]
  rw [hinv] at h
  have hlog : log (1.46 / (s - 1)) = log 1.46 - log (s - 1) :=
    Real.log_div (by norm_num) hs.ne'
  have h146 := log_one_four_six
  have h' : (1:ℝ) - (s - 1) * (1 / 1.46) ≤ log (1.46 / (s - 1)) := by
    have e : (s - 1) * (1 / 1.46) = (s - 1) / 1.46 := by rw [mul_one_div]
    rw [e]
    exact h
  have hle : log (s - 1) ≤ 0.3784365 - 1 + (s - 1) * (1 / 1.46) := by linarith
  have key : 0.3784365 + (s - 1) * (1 / 1.46) ≤ 0.56081 * s := by nlinarith
  linarith

private theorem q_lower_pos (s : ℝ) (h2 : 2.47 ≤ s) (h3 : s ≤ 3) :
    0 ≤ log (s - 1) - 0.56081 * s + 1 := by
  have h147 := log_one_four_seven
  have h16 := log_one_six
  have h18 := log_one_eight
  by_cases h : s ≤ 2.6
  · have hb := log_ge_linear 1.47 (s - 1) 1.6 (by norm_num) (by linarith) (by linarith)
    have key : 0.56081 * s - 1 ≤ 0.3852624 + (s - 1 - 1.47) * (1 / 1.6) := by nlinarith
    linarith
  · have h1 : 2.6 < s := not_le.mp h
    by_cases h' : s ≤ 2.8
    · have hb := log_ge_linear 1.6 (s - 1) 1.8 (by norm_num) (by linarith) (by linarith)
      have key : 0.56081 * s - 1 ≤ 0.4700036 + (s - 1 - 1.6) * (1 / 1.8) := by nlinarith
      linarith
    · have h2' : 2.8 < s := not_le.mp h'
      have hb := log_ge_linear 1.8 (s - 1) 2 (by norm_num) (by linarith) (by linarith)
      have key : 0.56081 * s - 1 ≤ 0.5877866 + (s - 1 - 1.8) * (1 / 2) := by nlinarith
      linarith

private theorem q_upper_nonpos (s : ℝ) (h2 : 2 ≤ s) (h3 : s ≤ 2.5) :
    log (s - 1) - 0.56439 * s + 1 ≤ 0 := by
  have h15 := log_one_five
  have hb := log_le_tangent 1.5 (s - 1) (by norm_num) (by linarith)
  have key : 0.4054652 - 1 + (s - 1 - 1.5) * (1 / 1.5) ≤ 0.56439 * s - 1 := by nlinarith
  linarith

private theorem q_upper_le (s : ℝ) (h2 : 2.5 ≤ s) (h3 : s ≤ 2.99) :
    log (s - 1) - 0.56439 * s + 1 ≤ 0.0117 := by
  have h175 := log_one_seven_five
  have hb := log_le_tangent 1.75 (s - 1) (by norm_num) (by linarith)
  have key : 0.5596158 + (s - 1 - 1.75) * (1 / 1.75) ≤ 0.56439 * s - 1 + 0.0117 := by nlinarith
  linarith

private theorem q_upper_small (s : ℝ) (h2 : 2.78 ≤ s) (h3 : s ≤ 3) :
    -(0.00003 : ℝ) ≤ log (s - 1) - 0.56439 * s + 1 := by
  have hs1 : 0 < s - 1 := by linarith
  have hs : 0 < 2 / (s - 1) := div_pos (by norm_num) hs1
  have h := Real.log_le_sub_one_of_pos hs
  have hlog : log (2 / (s - 1)) = log 2 - log (s - 1) := Real.log_div (by norm_num) hs1.ne'
  have hval : 2 / (s - 1) - 1 = (3 - s) / (s - 1) := by
    rw [eq_div_iff hs1.ne', sub_mul, one_mul, div_mul_cancel₀ (2:ℝ) (ne_of_gt hs1)]
    ring
  rw [hval] at h
  have h1 : log 2 - (3 - s) / (s - 1) ≤ log (s - 1) := by linarith
  have h2' : (3 - s) / (s - 1) ≤ 0.56439 * (3 - s) := by
    rw [div_le_iff₀ hs1]
    nlinarith [show (0 : ℝ) ≤ 3 - s by linarith,
      show (1 : ℝ) ≤ 0.56439 * (s - 1) by nlinarith]
  linarith [h1, h2', Real.log_two_gt_d9]
/-! ## The pointwise bounds on three through four -/

private theorem buchstab_ge_three_four (u : ℝ) (h3 : 3 ≤ u) (h4 : u ≤ 4) :
    0.56081 ≤ buchstab u := by
  have hu : 0 < u := by linarith
  have hs2 : 2 ≤ u - 1 := by linarith
  have hs3 : u - 1 ≤ 3 := by linarith
  rw [Endpoints578.buchstab_three_four u h3 h4, le_div_iff₀ hu]
  have h46 : (0.000045 : ℝ) ≤
      (∫ t in (2 : ℝ)..(2.46), log (t - 1) / t) - (0.56081 * (2.46 + 1) - 1 - log 2.46) := by
    have h1 := J_two_four_six.1
    have h2' := log_two_four_six.1
    linarith
  have h47 : (0.000033 : ℝ) ≤
      (∫ t in (2 : ℝ)..(2.47), log (t - 1) / t) - (0.56081 * (2.47 + 1) - 1 - log 2.47) := by
    have h1 := J_two_four_seven.1
    have h2' := log_two_four_seven.1
    linarith
  by_cases hc : u - 1 ≤ 2.46
  · have h := Phi_le_of_nonpos (c := 0.56081) (a := u - 1) (b := 2.46) hs2 hc (by norm_num)
      (fun t ht => q_lower_neg t (hs2.trans ht.1) ht.2)
    linarith
  · push_neg at hc
    by_cases hd : 2.47 ≤ u - 1
    · have h := Phi_le_of_nonneg (c := 0.56081) (a := 2.47) (b := u - 1) (by norm_num) hd hs3
        (fun t ht => q_lower_pos t ht.1 (ht.2.trans hs3))
      linarith
    · push_neg at hd
      have hP := Phi_sub_Phi (c := 0.56081) (a := 2.46) (b := u - 1) (by norm_num) hc.le hs3
      have hb : |∫ t in (2.46 : ℝ)..(u - 1), (log (t - 1) - 0.56081 * t + 1) / t|
          ≤ 0.000029 := by
        have hC : ‖∫ t in (2.46 : ℝ)..(u - 1), (log (t - 1) - 0.56081 * t + 1) / t‖
            ≤ 0.0029 * |(u - 1) - 2.46| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro t ht
          rw [Set.uIoc_of_le hc.le] at ht
          have ht1 : (2.46 : ℝ) ≤ t := ht.1.le
          have ht3 : t ≤ 2.47 := by linarith [ht.2]
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0:ℝ) < t)]
          have hq1 : log (t - 1) - 0.56081 * t + 1 ≤ 0.0068 := by
            have hl : log (t - 1) ≤ 0.3852625 := by
              have h2' := Real.log_le_log (by linarith : (0:ℝ) < t - 1)
                (by linarith : t - 1 ≤ 1.47)
              linarith [h2', log_one_four_seven.2]
            linarith
          have hq2 : -(0.0068 : ℝ) ≤ log (t - 1) - 0.56081 * t + 1 := by
            have hl : (0.3784364 : ℝ) ≤ log (t - 1) := by
              have h2' := Real.log_le_log (by norm_num : (0:ℝ) < 1.46)
                (by linarith : (1.46:ℝ) ≤ t - 1)
              linarith [h2', log_one_four_six.1]
            linarith
          have hqabs : |log (t - 1) - 0.56081 * t + 1| ≤ 0.0068 := by
            rw [abs_le]
            exact ⟨hq2, hq1⟩
          rw [div_le_iff₀ (by linarith : (0:ℝ) < t)]
          nlinarith [hqabs]
        rw [Real.norm_eq_abs] at hC
        have hle : |(u - 1) - 2.46| ≤ 0.01 := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        nlinarith [hC, hle]
      obtain ⟨hb1, hb2⟩ := abs_le.mp hb
      linarith

private theorem buchstab_le_three_four (u : ℝ) (h3 : 3 ≤ u) (h4 : u ≤ 4) :
    buchstab u ≤ 0.56439 := by
  have hu : 0 < u := by linarith
  have hs2 : 2 ≤ u - 1 := by linarith
  have hs3 : u - 1 ≤ 3 := by linarith
  rw [Endpoints578.buchstab_three_four u h3 h4, div_le_iff₀ hu]
  have h2 : (∫ t in (2 : ℝ)..(2:ℝ), log (t - 1) / t) - (0.56439 * (2 + 1) - 1 - log 2) ≤ 0 := by
    simp only [integral_same, zero_sub, neg_nonpos]
    linarith [Real.log_two_lt_d9]
  have h25 : (∫ t in (2 : ℝ)..(2.5), log (t - 1) / t) - (0.56439 * (2.5 + 1) - 1 - log 2.5)
      ≤ -(0.011 : ℝ) := by
    have h1 := J_two_five.2
    have h2' := log_two_five.2
    linarith
  have h3' : (∫ t in (2 : ℝ)..(3:ℝ), log (t - 1) / t) - (0.56439 * (3 + 1) - 1 - log 3)
      ≤ -(0.011 : ℝ) := by
    have h1 := Endpoints578.log_integral_at_four.2
    have h2' := log_three.2
    linarith
  by_cases hc : u - 1 ≤ 2.5
  · have h := Phi_le_of_nonpos (c := 0.56439) (a := 2) (b := u - 1) le_rfl hs2 hs3
      (fun t ht => q_upper_nonpos t ht.1 (ht.2.trans hc))
    linarith
  · push_neg at hc
    by_cases hc2 : u - 1 ≤ 2.99
    · have hP := Phi_sub_Phi (c := 0.56439) (a := 2.5) (b := u - 1) (by norm_num) hc.le hs3
      have hm : ∫ t in (2.5 : ℝ)..(u - 1), (log (t - 1) - 0.56439 * t + 1) / t ≤ 0.0024 := by
        have hmono : ∫ t in (2.5 : ℝ)..(u - 1), (log (t - 1) - 0.56439 * t + 1) / t ≤
            ∫ t in (2.5 : ℝ)..(u - 1), (0.00468 : ℝ) := by
          apply integral_mono_on (hab := hc.le) (hf := ?_) (hg := ?_)
          · intro t ht
            have ht1 : (2.5 : ℝ) ≤ t := ht.1
            have ht3 : t ≤ 2.99 := by linarith [ht.2]
            have hl := q_upper_le t ht1 ht3
            have ht0 : 0 < t := by linarith
            rw [div_le_iff₀ ht0]
            nlinarith
          · exact ContinuousOn.intervalIntegrable_of_Icc hc.le (by
              apply ContinuousOn.div
              · apply ContinuousOn.add
                · apply ContinuousOn.sub
                  · apply ContinuousOn.log (by fun_prop)
                    intro t ht
                    linarith [ht.1]
                  · fun_prop
                · fun_prop
              · fun_prop
              · intro t ht
                linarith [ht.1])
          · exact continuous_const.intervalIntegrable 2.5 (u - 1)
        have hconst : (∫ t in (2.5 : ℝ)..(u - 1), (0.00468 : ℝ)) = 0.00468 * ((u - 1) - 2.5) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        have hle : 0.00468 * ((u - 1) - 2.5) ≤ 0.0024 := by nlinarith
        linarith
      linarith
    · push_neg at hc2
      have hP := Phi_sub_Phi (c := 0.56439) (a := u - 1) (b := 3) hs2 hs3 (le_refl 3)
      have hb : |∫ t in (u - 1)..(3:ℝ), (log (t - 1) - 0.56439 * t + 1) / t|
          ≤ 0.0000026 := by
        have hC : ‖∫ t in (u - 1)..(3:ℝ), (log (t - 1) - 0.56439 * t + 1) / t‖
            ≤ 0.00022 * |3 - (u - 1)| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro t ht
          rw [Set.uIoc_of_le hs3] at ht
          have ht1 : (u - 1 : ℝ) ≤ t := ht.1.le
          have ht2 : t ≤ 3 := ht.2
          have ht3 : (2.99 : ℝ) ≤ t := by linarith [hc2.le, ht1]
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0:ℝ) < t)]
          have hup : log (t - 1) - 0.56439 * t + 1 ≤ 0.00063 := by
            have hb1 := log_le_tangent 2 (t - 1) (by norm_num) (by linarith)
            linarith [hb1, Real.log_two_lt_d9]
          have hlo : -(0.00003 : ℝ) ≤ log (t - 1) - 0.56439 * t + 1 :=
            q_upper_small t (by linarith) ht2
          have hqabs : |log (t - 1) - 0.56439 * t + 1| ≤ 0.00063 := by
            rw [abs_le]
            exact ⟨by linarith, hup⟩
          rw [div_le_iff₀ (by linarith : (0:ℝ) < t)]
          nlinarith [hqabs]
        rw [Real.norm_eq_abs] at hC
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 3 - (u - 1))] at hC
        have hle : 3 - (u - 1) ≤ 0.011 := by linarith
        nlinarith [hC, hle]
      obtain ⟨hb1, hb2⟩ := abs_le.mp hb
      linarith

end

/-- LEAF. Jia page 262 first finite base grid, restricted to the unresolved interior.
The two endpoint values at three and four are proved in Endpoints578.
Only the 9999 interior grid values remain in this proper input. -/
theorem grid_three_interior : ∀ k : ℕ, 0 < k → k < 10000 →
    0.56081 ≤ buchstab (3 + 0.0001 * (k : ℝ)) ∧
      buchstab (3 + 0.0001 * (k : ℝ)) ≤ 0.56439 := by
  intro k hk hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (k : ℝ) < 10000 := by exact_mod_cast hk2
  have h3 : 3 ≤ 3 + 0.0001 * (k : ℝ) := by linarith
  have h4 : 3 + 0.0001 * (k : ℝ) ≤ 4 := by linarith
  exact ⟨buchstab_ge_three_four _ h3 h4, buchstab_le_three_four _ h3 h4⟩


/-- LEAF. Jia page 262 second finite base grid after its proved initial endpoint.
The value at four is already certified. Only the remaining 10000 values are asserted. -/
theorem grid_four_tail : ∀ k : ℕ, 0 < k → k ≤ 10000 →
    0.5613 ≤ buchstab (4 + 0.0001 * (k : ℝ)) ∧
      buchstab (4 + 0.0001 * (k : ℝ)) ≤ 0.5616 := by sorry

/-- Jia page 262 proof of Lemma 20, the first two unnumbered finite grid bounds.
CONDITIONAL ON grid_three_interior only.
The function is the constructed solution of display 40. Only 10001 base values are asserted.
This is a proper finite input, not the global numerical conclusion. -/
theorem grid_three : ∀ k : ℕ, k ≤ 10000 →
    0.56081 ≤ buchstab (3 + 0.0001 * (k : ℝ)) ∧
      buchstab (3 + 0.0001 * (k : ℝ)) ≤ 0.56439 := by
  intro k hk
  by_cases hz : k = 0
  · subst k
    simpa using Endpoints578.grid_three_start
  by_cases ht : k = 10000
  · subst k
    norm_num only
    have h := Endpoints578.grid_four_start
    constructor <;> linarith [h.1, h.2]
  exact grid_three_interior k (by omega) (by omega)

/-- Jia page 262 proof of Lemma 20, the second pair of unnumbered finite grid bounds.
CONDITIONAL ON grid_four_tail only.
Only the printed base grid on four through five is asserted, with its original constants. -/
theorem grid_four : ∀ k : ℕ, k ≤ 10000 →
    0.5613 ≤ buchstab (4 + 0.0001 * (k : ℝ)) ∧
      buchstab (4 + 0.0001 * (k : ℝ)) ≤ 0.5616 := by
  intro k hk
  by_cases hz : k = 0
  · subst k
    simpa using Endpoints578.grid_four_start
  exact grid_four_tail k (by omega) hk

/-- Page 262 interpolation support: the constructed function is 0.0224 Lipschitz above three. -/
theorem buchstab_lipschitz (x y : ℝ) (hx : 3 ≤ x) (hy : 3 ≤ y) :
    |buchstab x - buchstab y| ≤ 0.0224 * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Ici (3 : ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (buchstab_derivative z (by linarith [show (3 : ℝ) ≤ z from hz])).differentiableAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using buchstab_derivative_0224 z hz) hy hx

/-- Page 262: the source grid mesh loses at most 0.00000224 between a grid point and a real argument.
CONDITIONAL ON the supplied finite grid bounds. -/
theorem grid_interpolation (a l U : ℝ) (ha : 3 ≤ a)
    (hgrid : ∀ k : ℕ, k ≤ 10000 → l ≤ buchstab (a + 0.0001 * (k : ℝ)) ∧
      buchstab (a + 0.0001 * (k : ℝ)) ≤ U)
    (u : ℝ) (hu : a ≤ u) (hu1 : u ≤ a + 1) :
    l - 0.00000224 ≤ buchstab u ∧ buchstab u ≤ U + 0.00000224 := by
  let k := ⌊10000 * (u - a)⌋₊
  have hk : k ≤ 10000 := by
    calc k ≤ ⌊(10000 : ℝ)⌋₊ := Nat.floor_mono (by linarith)
         _ = 10000 := by norm_num
  have hkl := Nat.floor_le (show 0 ≤ 10000 * (u - a) by positivity)
  have hku := Nat.lt_floor_add_one (10000 * (u - a))
  have hgL : a + 0.0001 * (k : ℝ) ≤ u := by dsimp [k]; linarith
  have hgU : u - (a + 0.0001 * (k : ℝ)) ≤ 0.0001 := by dsimp [k]; linarith
  have hg3 : 3 ≤ a + 0.0001 * (k : ℝ) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hd := buchstab_lipschitz u (a + 0.0001 * (k : ℝ)) (ha.trans hu) hg3
  rw [abs_of_nonneg (sub_nonneg.mpr hgL)] at hd
  have he : |buchstab u - buchstab (a + 0.0001 * (k : ℝ))| ≤ 0.00000224 := by
    nlinarith
  have hb := hgrid k hk
  obtain ⟨heL, heU⟩ := abs_le.mp he
  constructor <;> linarith [hb.1, hb.2]

/-- Display 41 support: reuse the existing weighted strip comparison at an arbitrary starting interval.
CONDITIONAL ON the stated bounds on that one interval. -/
theorem bounds_propagate (K l U : ℝ) (hK : 2 ≤ K)
    (hbase : ∀ u ∈ Set.Icc K (K + 1), l ≤ buchstab u ∧ buchstab u ≤ U) :
    ∀ u : ℝ, K ≤ u → l ≤ buchstab u ∧ buchstab u ≤ U := by
  have hstrip : ∀ j : ℕ, ∀ u ∈ Set.Icc (K + (j : ℝ)) (K + (j : ℝ) + 1),
      l ≤ buchstab u ∧ buchstab u ≤ U := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      intro u hu
      simp only [Nat.cast_add, Nat.cast_one] at hu
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hKu : K + (j : ℝ) + 1 ≤ u := by linarith [hu.1]
      have hKp : 0 < K + (j : ℝ) + 1 := by linarith
      have hw := ih (K + (j : ℝ) + 1) ⟨by linarith, le_rfl⟩
      have hi := buchstab_continuous.intervalIntegrable (μ := MeasureTheory.volume)
        ((K + (j : ℝ) + 1) - 1) (u - 1)
      have hb : ∀ t ∈ Set.Icc ((K + (j : ℝ) + 1) - 1) (u - 1),
          l ≤ buchstab t ∧ buchstab t ≤ U := by
        intro t ht
        exact ih t ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩
      exact buchstab_strip_from_recurrence buchstab (K + (j : ℝ) + 1) u l U
        hKp hKu hw hi hb (buchstab_anchored_recurrence _ _ (by linarith) hKu)
  intro u hu
  let j := ⌊u - K⌋₊
  have hjL := Nat.floor_le (show 0 ≤ u - K by linarith)
  have hjU := Nat.lt_floor_add_one (u - K)
  exact hstrip j u ⟨by dsimp [j]; linarith, by dsimp [j]; linarith⟩

/-- Page 262 Lemma 20 part ii: interpolate and propagate the first finite base grid.
CONDITIONAL ON grid_three only. -/
theorem global_three_from_grid : ∀ u : ℝ, 3 ≤ u →
    0.5607 ≤ buchstab u ∧ buchstab u ≤ 0.5644 := by
  apply bounds_propagate 3 0.5607 0.5644 (by norm_num)
  intro u hu
  have h := grid_interpolation 3 0.56081 0.56439 (by norm_num) grid_three u hu.1 hu.2
  constructor <;> linarith [h.1, h.2]

/-- Page 262 Lemma 20 part iii: interpolate and propagate the second finite base grid.
CONDITIONAL ON grid_four only. -/
theorem global_four_from_grid : ∀ u : ℝ, 4 ≤ u →
    0.5612 ≤ buchstab u ∧ buchstab u ≤ 0.5617 := by
  apply bounds_propagate 4 0.5612 0.5617 (by norm_num)
  intro u hu
  have h := grid_interpolation 4 0.5613 0.5616 (by norm_num) grid_four u hu.1 hu.2
  constructor <;> linarith [h.1, h.2]

/-- Jia Lemma 20 parts ii and iii: every source solution obeys the required global bounds.
CONDITIONAL ON the two proper finite grid leaves only. -/
theorem lemma20_bounds_from_grids :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t) →
      (∀ u : ℝ, 3 ≤ u → w u ≤ 0.5644) ∧
      (∀ u : ℝ, 4 ≤ u → 0.5612 ≤ w u ∧ w u ≤ 0.5617) := by
  intro w hc h0 hr
  have he := solution_eq_buchstab w h0 hr
  constructor
  · intro u hu
    rw [he u (by linarith)]
    exact (global_three_from_grid u hu).2
  · intro u hu
    rw [he u (by linarith)]
    exact global_four_from_grid u hu

#print axioms grid_three_interior
#print axioms grid_four_tail
#print axioms grid_three
#print axioms grid_four
#print axioms buchstab_lipschitz
#print axioms grid_interpolation
#print axioms bounds_propagate
#print axioms global_three_from_grid
#print axioms global_four_from_grid
#print axioms lemma20_bounds_from_grids
end
end LeanLab.Languasco2004.Decomp578e
