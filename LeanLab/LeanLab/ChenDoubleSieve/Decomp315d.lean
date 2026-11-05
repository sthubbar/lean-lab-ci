import LeanLab.ChenDoubleSieve.Decomp275i

/-!
Supply split for Wu 2004 Section 10.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- Split the upper sieve coefficient at three using both known local formulas.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem upper_weighted_split {F f : ℝ → ℝ} (h : IsLinearSieve F f)
    {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    4 / exp eulerMascheroniConstant *
      (∫ t in a..5, F t / (1 - t / 6)) =
    8 * (∫ t in a..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  have hFi : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume a 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : a ≤ 5)]
    refine (h.1.mono (fun t ht => ?_)).div (by fun_prop) ?_
    · change 0 < t
      linarith [ht.1]
    · intro t ht
      linarith [ht.2]
  have hi₁ : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume a 3 := by
    apply hFi.mono_set
    rw [Set.uIcc_of_le ha3, Set.uIcc_of_le (by linarith : a ≤ 5)]
    exact Set.Icc_subset_Icc_right (by norm_num)
  have hi₂ : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume 3 5 := by
    apply hFi.mono_set
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5),
      Set.uIcc_of_le (by linarith : a ≤ 5)]
    exact Set.Icc_subset_Icc_left ha3
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, mul_add]
  have hsmall : (∫ t in a..3, F t / (1 - t / 6)) =
      (2 * exp eulerMascheroniConstant) * ∫ t in a..3, 1 / (t * (1 - t / 6)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha3] at ht
    dsimp only
    rw [Task275.linear_upper_three h (by linarith [ht.1]) ht.2]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hlarge : (∫ t in (3 : ℝ)..5, F t / (1 - t / 6)) =
      (2 * exp eulerMascheroniConstant) * ∫ t in (3 : ℝ)..5,
        (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at ht
    dsimp only
    rw [Task275.linear_upper_five h ht]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsmall, hlarge]
  field_simp [Real.exp_ne_zero]
  <;> ring

/-- The actual F2 coefficient has an elementary split at the sieve transition.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F2_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 2 =
    8 * (∫ t in (258 / 125 : ℝ)..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  change 4 / exp eulerMascheroniConstant *
    (∫ t in ((1 / 2 - sigma1) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t)) = _
  norm_num only [kappa1, sigma1, show (1 / 2 - 41 / 125 : ℝ) / (1 / 12) = 258 / 125 by norm_num,
    show (1 / 2 - 1 / 12 : ℝ) / (1 / 12) = 5 by norm_num]
  convert upper_weighted_split h (a := 258 / 125) (by norm_num) (by norm_num) using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- The actual F3 coefficient shares the same upper tail as F2.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F3_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 3 =
    8 * (∫ t in (327 / 125 : ℝ)..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  change 4 / exp eulerMascheroniConstant *
    (∫ t in ((1 / 2 - sigma2) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t)) = _
  norm_num only [kappa1, sigma2, show (1 / 2 - 141 / 500 : ℝ) / (1 / 12) = 327 / 125 by norm_num,
    show (1 / 2 - 1 / 12 : ℝ) / (1 / 12) = 5 by norm_num]
  convert upper_weighted_split h (a := 327 / 125) (by norm_num) (by norm_num) using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- The elementary part of F2 and F3 has an exact logarithmic antiderivative.
Source: page 39 equation 10.4, derived integration helper. -/
theorem reciprocal_head {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    (∫ t in a..3, 1 / (t * (1 - t / 6))) = log ((6 - a) / a) := by
  have hcont₁ : ContinuousOn (fun t : ℝ => (1 : ℝ) / t) (Set.uIcc a 3) := by
    rw [Set.uIcc_of_le ha3]
    refine continuousOn_const.div continuousOn_id ?_
    intro t ht
    linarith [ht.1]
  have hcont₂ : ContinuousOn (fun t : ℝ => (1 : ℝ) / (6 - t)) (Set.uIcc a 3) := by
    rw [Set.uIcc_of_le ha3]
    refine continuousOn_const.div (by fun_prop) ?_
    intro t ht
    linarith [ht.2]
  have he : (∫ t in a..3, 1 / (t * (1 - t / 6))) =
      (∫ t in a..3, 1 / t) + ∫ t in a..3, 1 / (6 - t) := by
    rw [← intervalIntegral.integral_add hcont₁.intervalIntegrable hcont₂.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha3] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht6 : 6 - t ≠ 0 := by linarith [ht.2]
    have htden : 1 - t / 6 ≠ 0 := by linarith [ht.2]
    field_simp [ht0, ht6, htden]
    <;> ring
  rw [he]
  simp only [one_div]
  rw [integral_inv_of_pos ha (by norm_num),
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 6]
  norm_num only [show (6 - 3 : ℝ) = 3 by norm_num]
  rw [integral_inv_of_pos (by norm_num) (by linarith : 0 < 6 - a),
    Real.log_div (by norm_num : (3 : ℝ) ≠ 0) ha.ne',
    Real.log_div (by linarith : 6 - a ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_div (by linarith : 6 - a ≠ 0) ha.ne']
  ring

/-- F2 and F3 differ only by an elementary logarithmic head.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F2_sub_F3 {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 2 - integralTerms F f ω 3 =
      8 * (log (82 / 43 : ℝ) - log (141 / 109 : ℝ)) := by
  rw [F2_elementary h ω, F3_elementary h ω,
    reciprocal_head (a := 258 / 125) (by norm_num) (by norm_num),
    reciprocal_head (a := 327 / 125) (by norm_num) (by norm_num)]
  norm_num only [show (6 - 258 / 125 : ℝ) / (258 / 125) = 82 / 43 by norm_num,
    show (6 - 327 / 125 : ℝ) / (327 / 125) = 141 / 109 by norm_num]
  ring

set_option maxHeartbeats 2000000

/-! ### Rational logarithm series, cast to the reals -/

section quadrature

open Set Filter Topology
open intervalIntegral

private lemma rat_logLower_cast (N : ℕ) (y : ℚ) :
    ((∑ j ∈ range N, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1) : ℚ) : ℝ) =
      ∑ j ∈ range N, (((y : ℝ) - 1) / ((y : ℝ) + 1)) ^ (2 * j + 1) / (2 * j + 1) := by
  push_cast
  rfl

private lemma rat_logUpper_cast (N : ℕ) (y : ℚ) :
    ((2 * (∑ j ∈ range N, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1) : ℚ)
        + 2 * ((y - 1) / (y + 1)) ^ (2 * N + 1) / (1 - ((y - 1) / (y + 1)) ^ 2) : ℚ) : ℝ) =
      Wu04Integral.logUpper N (y : ℝ) := by
  rw [Wu04Integral.logUpper, Wu04Integral.logLower]
  push_cast
  ring

private lemma rat_logLower_cast' (N : ℕ) (y : ℚ) :
    ((2 * (∑ j ∈ range N, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1)) : ℚ) : ℝ) =
      Wu04Integral.logLower N (y : ℝ) := by
  rw [Wu04Integral.logLower]
  push_cast
  ring

/-! ### Two-sided polynomial bounds for `log` on `[0, 1/2]` -/

private lemma log_one_add_abs {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    |Real.log (1 + s) - ∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)|
      ≤ 2 * s ^ (n + 1) := by
  have hx : |-s| < 1 := by
    rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have hsum : (∑ i ∈ range n, (-s) ^ (i + 1) / (i + 1) : ℝ)
      = -(∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_pow]
    have : (-1 : ℝ) ^ (i + 1) = -((-1) ^ i) := by
      rw [pow_succ]
      ring
    rw [this]
    ring
  have h1s : (1 : ℝ) - -s = 1 + s := by ring
  rw [hsum, h1s, abs_neg, abs_of_nonneg h0] at h
  calc |Real.log (1 + s) - ∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)|
      = |-(∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) + Real.log (1 + s)| := by
        rw [neg_add_eq_sub, abs_sub_comm]
    _ ≤ s ^ (n + 1) / (1 - s) := h
    _ ≤ 2 * s ^ (n + 1) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg h0 (n + 1), h0]

private lemma log_one_add_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    Real.log (1 + s) ≤ (∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) + 2 * s ^ (n + 1) := by
  have h := (abs_le.mp (log_one_add_abs h0 h1 n)).2
  linarith

private lemma log_one_add_ge {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    (∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) - 2 * s ^ (n + 1) ≤ Real.log (1 + s) := by
  have h := (abs_le.mp (log_one_add_abs h0 h1 n)).1
  linarith

private lemma log_one_add_ge9 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) - 2 * u ^ 9 ≤ Real.log (1 + u) := by
  have h := log_one_add_ge (s := u) h0 h1 8
  simpa using h

private lemma log_one_add_le9 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    Real.log (1 + u) ≤ (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) + 2 * u ^ 9 := by
  have h := log_one_add_le (s := u) h0 h1 8
  simpa using h

private lemma log_one_sub_abs {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    |Real.log (1 - s) + ∑ i ∈ range n, s ^ (i + 1) / (i + 1)| ≤ 2 * s ^ (n + 1) := by
  have hx : |s| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have h1s : (1 : ℝ) - s = 1 - s := rfl
  rw [h1s, abs_of_nonneg h0] at h
  calc |Real.log (1 - s) + ∑ i ∈ range n, s ^ (i + 1) / (i + 1)|
      = |(∑ i ∈ range n, s ^ (i + 1) / (i + 1)) + Real.log (1 - s)| := by rw [add_comm]
    _ ≤ s ^ (n + 1) / (1 - s) := h
    _ ≤ 2 * s ^ (n + 1) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg h0 (n + 1), h0]

private lemma log_one_sub_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    Real.log (1 - s) ≤ -(∑ i ∈ range n, s ^ (i + 1) / (i + 1)) + 2 * s ^ (n + 1) := by
  have h := (abs_le.mp (log_one_sub_abs h0 h1 n)).2
  linarith

private lemma log_one_sub_ge {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    -(∑ i ∈ range n, s ^ (i + 1) / (i + 1)) - 2 * s ^ (n + 1) ≤ Real.log (1 - s) := by
  have h := (abs_le.mp (log_one_sub_abs h0 h1 n)).1
  linarith

private lemma inv_geom_bounds {p h : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hs : h ≤ p / 2) (L : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) h) :
    (∑ l ∈ range (L + 1), (-(t / p)) ^ l) * (1 / p) - (1 / p) * ((h / p) ^ (L + 1) / (1 - h / p))
        ≤ 1 / (p + t) ∧
      1 / (p + t) ≤
        (∑ l ∈ range (L + 1), (-(t / p)) ^ l) * (1 / p) + (1 / p) * ((h / p) ^ (L + 1) / (1 - h / p)) := by
  have hpne : p ≠ 0 := hp.ne'
  have hu0 : 0 ≤ t / p := div_nonneg ht.1 hp.le
  have huh : t / p ≤ h / p := by gcongr; exact ht.2
  have hhr : h / p ≤ 1 / 2 := by rw [div_le_iff₀ hp]; linarith
  have hpos : (0 : ℝ) < 1 - h / p := by linarith
  have h2 : (0:ℝ) < 1 + t / p := by linarith
  -- geometric identity
  have hne : (-(t / p) - 1) ≠ 0 := by
    have h : -(t / p) - 1 = -(1 + t / p) := by ring
    rw [h]; exact neg_ne_zero.mpr h2.ne'
  have hval : (∑ l ∈ range (L + 1), (-(t / p)) ^ l) = ((-(t / p)) ^ (L + 1) - 1) / (-(t / p) - 1) := by
    rw [eq_div_iff hne]
    simpa only [mul_comm] using geom_sum_mul (-(t / p)) (L + 1)
  have hgeom : (∑ l ∈ range (L + 1), (-(t / p)) ^ l) + (-(t / p)) ^ (L + 1) / (1 + t / p)
      = 1 / (1 + t / p) := by
    rw [hval, show (-(t / p)) - 1 = -(1 + t / p) by ring, div_neg]
    field_simp
    ring
  have habs : |(-(t / p)) ^ (L + 1) / (1 + t / p)| ≤ (h / p) ^ (L + 1) / (1 - h / p) := by
    have h3 : 1 - h / p ≤ 1 + t / p := by linarith
    rw [abs_div, abs_pow, abs_neg, abs_of_nonneg hu0, abs_of_pos h2]
    exact div_le_div₀ (pow_nonneg (by positivity : (0:ℝ) ≤ h / p) _) (pow_le_pow_left₀ hu0 huh _) hpos h3
  have hkey : 1 / (p + t) = (1 / p) * (∑ l ∈ range (L + 1), (-(t / p)) ^ l)
      + (1 / p) * ((-(t / p)) ^ (L + 1) / (1 + t / p)) := by
    have hpt : p + t = p * (1 + t / p) := by field_simp
    have hsplit : 1 / (p * (1 + t / p)) = (1 / p) * (1 / (1 + t / p)) := by
      field_simp
    rw [hpt, hsplit, ← hgeom]
    ring
  have hpp : (0:ℝ) < 1 / p := by positivity
  constructor
  · rw [hkey]
    have h := neg_abs_le ((-(t / p)) ^ (L + 1) / (1 + t / p))
    nlinarith
  · rw [hkey]
    have h := le_abs_self ((-(t / p)) ^ (L + 1) / (1 + t / p))
    nlinarith

private lemma contAt_of_contOn {f : ℝ → ℝ} {a b x : ℝ} (ha : a ≤ b)
    (h : ContinuousOn f (uIcc a b)) (hx : x ∈ Ioo a b) : ContinuousAt f x :=
  h.continuousAt (by rw [Set.uIcc_of_le ha]; exact Icc_mem_nhds hx.1 hx.2)

private lemma triangle_swap {f h : ℝ → ℝ} {c A B : ℝ}
    (hc : 0 ≤ c) (hAB : A ≤ B - c)
    (hf : ContinuousOn f (uIcc (A - c) (B - c))) (hh : ContinuousOn h (uIcc A B)) :
    ∫ t in A..B, (∫ x in (A - c)..(t - c), f x) * h t
      = ∫ x in (A - c)..(B - c), f x * (∫ t in (x + c)..B, h t) := by
  have hAc : A - c ≤ B - c := by linarith
  have hAB' : A ≤ B := by linarith
  set F : ℝ → ℝ := fun x => ∫ s in (A - c)..x, f s with hFdef
  set K : ℝ → ℝ := fun s => ∫ t in A..s, h t with hKdef
  have hfi : IntervalIntegrable f volume (A - c) (B - c) := hf.intervalIntegrable
  have hhi : IntervalIntegrable h volume A B := hh.intervalIntegrable
  have hFc : ContinuousOn F (uIcc (A - c) (B - c)) := by
    rw [hFdef]; exact continuousOn_primitive_interval' hfi (Set.left_mem_uIcc)
  have hKc : ContinuousOn K (uIcc A B) := by
    rw [hKdef]; exact continuousOn_primitive_interval' hhi (Set.left_mem_uIcc)
  -- continuity of the two integrands on the full interval
  have hφc : ContinuousOn (fun t => F (t - c) * h t) (uIcc A B) := by
    refine ContinuousOn.mul ?_ hh
    refine hFc.comp (by fun_prop) ?_
    intro t ht
    rw [Set.uIcc_of_le hAB'] at ht
    rw [Set.uIcc_of_le hAc]
    constructor <;> linarith [ht.1, ht.2]
  have hgc : ContinuousOn (fun x => f x * K (x + c)) (uIcc (A - c) (B - c)) := by
    refine ContinuousOn.mul hf ?_
    refine hKc.comp (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le hAc] at hx
    rw [Set.uIcc_of_le hAB']
    constructor <;> linarith [hx.1, hx.2, hc]
  have hφi : ∀ {u v : ℝ}, A ≤ u → u ≤ v → v ≤ B → IntervalIntegrable (fun t => F (t - c) * h t) volume u v := by
    intro u v h1 h2 h3
    apply (hφc.mono ?_).intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le h2] at ht
    rw [Set.uIcc_of_le hAB']
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgi : IntervalIntegrable (fun x => f x * K (x + c)) volume (A - c) (B - c) :=
    hgc.intervalIntegrable
  have hhi' : ∀ {u v : ℝ}, A ≤ u → u ≤ v → v ≤ B → IntervalIntegrable h volume u v := by
    intro u v hu huv hvB
    apply (hh.mono ?_).intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    rw [Set.uIcc_of_le hAB']
    exact ⟨by linarith [ht.1, hu], by linarith [ht.2, hvB]⟩
  have hgi' : ∀ {v : ℝ}, A - c ≤ v → v ≤ B - c →
      IntervalIntegrable (fun x => f x * K (x + c)) volume (A - c) v := by
    intro v hv1 hv2
    apply (hgc.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hv1] at hx
    rw [Set.uIcc_of_le hAc]
    exact ⟨hx.1, by linarith [hx.2]⟩
  -- derivative of the outer primitive
  have dG : ∀ y ∈ Ioo A B,
      HasDerivAt (fun y => ∫ t in A..y, F (t - c) * h t) (F (y - c) * h y) y := by
    intro y hy
    have hcy : ContinuousAt (fun t => F (t - c) * h t) y := by
      refine ContinuousAt.mul ?_ (contAt_of_contOn hAB' hh hy)
      exact (contAt_of_contOn hAc hFc ⟨by linarith [hy.1], by linarith [hy.2]⟩).comp
        (by fun_prop : ContinuousAt (fun t : ℝ => t - c) y)
    have hφopen : ContinuousOn (fun t => F (t - c) * h t) (Ioo A B) := by
      refine hφc.mono ?_
      intro t ht
      rw [Set.uIcc_of_le hAB']
      exact ⟨ht.1.le, ht.2.le⟩
    have hsm : StronglyMeasurableAtFilter (fun t => F (t - c) * h t) (𝓝 y) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hφopen y hy
    exact integral_hasDerivAt_right (hφi le_rfl (le_of_lt hy.1) (le_of_lt hy.2)) hsm hcy
  -- derivative of the inner primitive
  have dPrim : ∀ y ∈ Ioo A B,
      HasDerivAt (fun y => ∫ x in (A - c)..(y - c), f x * K (x + c)) (f (y - c) * K y) y := by
    intro y hy
    have hyc : y - c ∈ Ioo (A - c) (B - c) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hcy : ContinuousAt (fun x => f x * K (x + c)) (y - c) := by
      refine ContinuousAt.mul (contAt_of_contOn hAc hf hyc) ?_
      exact (contAt_of_contOn hAB' hKc ⟨by linarith [hyc.1], by linarith [hyc.2, hc]⟩).comp
        (by fun_prop : ContinuousAt (fun x : ℝ => x + c) (y - c))
    have hgopen : ContinuousOn (fun x => f x * K (x + c)) (Ioo (A - c) (B - c)) := by
      refine hgc.mono ?_
      intro t ht
      rw [Set.uIcc_of_le hAc]
      exact ⟨ht.1.le, ht.2.le⟩
    have hsm : StronglyMeasurableAtFilter (fun x => f x * K (x + c)) (𝓝 (y - c)) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hgopen (y - c) hyc
    have h1 : HasDerivAt (fun z => ∫ x in (A - c)..z, f x * K (x + c))
        (f (y - c) * K (y - c + c)) (y - c) :=
      integral_hasDerivAt_right (hgi' (by linarith [hyc.1]) (by linarith [hyc.2])) hsm hcy
    have h2 : HasDerivAt (fun y : ℝ => y - c) 1 y := by
      simpa using (hasDerivAt_id y).sub_const c
    simpa [Function.comp_def, sub_add_cancel] using h1.comp y h2
  -- derivative of F ∘ (· - c)
  have dFc : ∀ y ∈ Ioo A B, HasDerivAt (fun y => F (y - c)) (f (y - c)) y := by
    intro y hy
    have hyc : y - c ∈ Ioo (A - c) (B - c) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hcy : ContinuousAt f (y - c) := contAt_of_contOn hAc hf hyc
    have hfopen : ContinuousOn f (Ioo (A - c) (B - c)) := by
      refine hf.mono ?_
      intro t ht
      rw [Set.uIcc_of_le hAc]
      exact ⟨ht.1.le, ht.2.le⟩
    have hsm : StronglyMeasurableAtFilter f (𝓝 (y - c)) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hfopen (y - c) hyc
    have h1 : HasDerivAt F (f (y - c)) (y - c) := by
      rw [hFdef]
      have hv : IntervalIntegrable f volume (A - c) (y - c) := by
        apply (hf.mono ?_).intervalIntegrable
        intro t ht
        rw [Set.uIcc_of_le (by linarith [hyc.1])] at ht
        rw [Set.uIcc_of_le hAc]
        exact ⟨ht.1, by linarith [ht.2, hyc.2]⟩
      exact integral_hasDerivAt_right hv hsm hcy
    have h2 : HasDerivAt (fun y : ℝ => y - c) 1 y := by
      simpa using (hasDerivAt_id y).sub_const c
    simpa [Function.comp_def] using h1.comp y h2
  have dK : ∀ y ∈ Ioo A B, HasDerivAt K (h y) y := by
    intro y hy
    have hcy : ContinuousAt h y := contAt_of_contOn hAB' hh hy
    have hhy : IntervalIntegrable h volume A y := hhi' (u := A) (v := y) le_rfl (le_of_lt hy.1) (le_of_lt hy.2)
    have hhopen : ContinuousOn h (Ioo A B) := by
      refine hh.mono ?_
      intro t ht
      rw [Set.uIcc_of_le hAB']
      exact ⟨ht.1.le, ht.2.le⟩
    have hsm : StronglyMeasurableAtFilter h (𝓝 y) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hhopen y hy
    rw [hKdef]
    exact integral_hasDerivAt_right hhy hsm hcy
  -- continuity of the difference function on [A,B]
  have hWcont : ContinuousOn
      (fun y => (∫ t in A..y, F (t - c) * h t)
        - ((∫ t in A..y, h t) * F (y - c) - ∫ x in (A - c)..(y - c), f x * K (x + c)))
      (Icc A B) := by
    have h1 : ContinuousOn (fun y => ∫ t in A..y, F (t - c) * h t) (Icc A B) := by
      have h := continuousOn_primitive_interval' (hφi le_rfl hAB' le_rfl) (Set.left_mem_uIcc (a := A) (b := B))
      rwa [Set.uIcc_of_le hAB'] at h
    have h2 : ContinuousOn (fun y => ∫ t in A..y, h t) (Icc A B) := by
      have h := continuousOn_primitive_interval' hhi (Set.left_mem_uIcc (a := A) (b := B))
      rwa [Set.uIcc_of_le hAB'] at h
    have h3 : ContinuousOn (fun y => F (y - c)) (Icc A B) := by
      refine hFc.comp (by fun_prop) ?_
      intro y hy
      rw [Set.uIcc_of_le hAc]
      constructor <;> linarith [hy.1, hy.2]
    have h4 : ContinuousOn (fun y => ∫ x in (A - c)..(y - c), f x * K (x + c)) (Icc A B) := by
      have hb := continuousOn_primitive_interval' hgi (Set.left_mem_uIcc (a := A - c) (b := B - c))
      have hcomp : (fun y : ℝ => ∫ x in (A - c)..(y - c), f x * K (x + c))
          = (fun y : ℝ => (fun z => ∫ x in (A - c)..z, f x * K (x + c)) (y - c)) := rfl
      rw [hcomp]
      refine hb.comp (by fun_prop) ?_
      intro y hy
      rw [Set.uIcc_of_le hAc]
      constructor <;> linarith [hy.1, hy.2]
    exact h1.sub ((h2.mul h3).sub h4)
  -- zero derivative in the interior
  have hWderiv : ∀ y ∈ Ioo A B,
      HasDerivAt (fun y => (∫ t in A..y, F (t - c) * h t)
        - ((∫ t in A..y, h t) * F (y - c) - ∫ x in (A - c)..(y - c), f x * K (x + c))) 0 y := by
    intro y hy
    have h1 := dG y hy
    have h2 := (dK y hy).mul (dFc y hy)
    have h3 := dPrim y hy
    have hd := h1.sub (h2.sub h3)
    have hval : F (y - c) * h y - (h y * F (y - c) + K y * f (y - c) - f (y - c) * K y) = 0 := by
      ring
    rw [← hval]
    exact hd
  -- conclude
  have key : (∫ t in A..B, F (t - c) * h t)
      = (∫ t in A..B, h t) * F (B - c) - ∫ x in (A - c)..(B - c), f x * K (x + c) := by
    have hzero : (∫ y in A..B, (0 : ℝ)) = (fun y => (∫ t in A..y, F (t - c) * h t)
        - ((∫ t in A..y, h t) * F (y - c) - ∫ x in (A - c)..(y - c), f x * K (x + c))) B
        - (fun y => (∫ t in A..y, F (t - c) * h t)
        - ((∫ t in A..y, h t) * F (y - c) - ∫ x in (A - c)..(y - c), f x * K (x + c))) A :=
      integral_eq_sub_of_hasDerivAt_of_le hAB' hWcont hWderiv intervalIntegrable_const
    simp only [intervalIntegral.integral_zero] at hzero
    have hA : (∫ t in A..A, F (t - c) * h t)
        - ((∫ t in A..A, h t) * F (A - c) - ∫ x in (A - c)..(A - c), f x * K (x + c)) = 0 := by
      simp
    have hB : (∫ t in A..B, F (t - c) * h t)
        - ((∫ t in A..B, h t) * F (B - c) - ∫ x in (A - c)..(B - c), f x * K (x + c)) = 0 := by
      linarith [hzero, hA]
    linarith [hB]
  have goal_eq : (∫ t in A..B, (∫ x in (A - c)..(t - c), f x) * h t)
      = ∫ t in A..B, F (t - c) * h t := by
    apply intervalIntegral.integral_congr
    intro t _
    rw [hFdef]
  rw [goal_eq, key]
  have hFB : F (B - c) = ∫ s in (A - c)..(B - c), f s := by rw [hFdef]
  have hstep : ∀ x ∈ uIcc (A - c) (B - c), (∫ t in (x + c)..B, h t) = (∫ t in A..B, h t) - K (x + c) := by
    intro x hx
    rw [Set.uIcc_of_le hAc] at hx
    have hAx : A ≤ x + c := by linarith [hx.1]
    have hxB : x + c ≤ B := by linarith [hx.2]
    rw [hKdef]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hhi' (u := A) (v := x + c) le_rfl hAx hxB) (hhi' (u := x + c) (v := B) hAx hxB le_rfl)]
    ring
  have hFac : (∫ t in A..B, h t) * (∫ s in (A - c)..(B - c), f s)
      = ∫ x in (A - c)..(B - c), f x * (∫ t in A..B, h t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hexp : (∫ x in (A - c)..(B - c), f x * (∫ t in (x + c)..B, h t))
      = ∫ x in (A - c)..(B - c), (f x * (∫ t in A..B, h t) - f x * K (x + c)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    show f x * (∫ t in (x + c)..B, h t) = f x * (∫ t in A..B, h t) - f x * K (x + c)
    rw [hstep x hx]
    ring
  rw [hFB, hexp, intervalIntegral.integral_sub (hfi.mul_const _) hgi, hFac]

private lemma int_pow_sub (p q : ℝ) (k : ℕ) :
    (∫ x in p..q, (x - p) ^ k) = (q - p) ^ (k + 1) / (k + 1) := by
  have h := intervalIntegral.integral_comp_sub_right (a := p) (b := q) (fun y : ℝ => y ^ k) p
  rw [show p - p = 0 by ring] at h
  rw [h, integral_pow]
  ring

private lemma poly3_eq (p x : ℝ) (A B C : ℕ → ℝ) (na nb nc : ℕ) :
    (∑ i ∈ range na, A i * (x - p) ^ i) * (∑ j ∈ range nb, B j * (x - p) ^ j) *
        (∑ l ∈ range nc, C l * (x - p) ^ l)
      = ∑ l ∈ range nc, ∑ j ∈ range nb, ∑ i ∈ range na,
          A i * B j * C l * (x - p) ^ (i + j + l) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun i _ => ?_)))
  have h : (x - p) ^ (i + j + l) = (x - p) ^ i * (x - p) ^ j * (x - p) ^ l := by
    rw [pow_add, pow_add]
  rw [h]
  ring

private lemma int_prod3 (p q : ℝ) (hpq : p ≤ q) (A B C : ℕ → ℝ) (na nb nc : ℕ) :
    (∫ x in p..q, (∑ i ∈ range na, A i * (x - p) ^ i) * (∑ j ∈ range nb, B j * (x - p) ^ j) *
        (∑ l ∈ range nc, C l * (x - p) ^ l))
      = ∑ l ∈ range nc, ∑ j ∈ range nb, ∑ i ∈ range na,
          A i * B j * C l * ((q - p) ^ (i + j + l + 1) / (i + j + l + 1)) := by
  have hcongr : (∫ x in p..q, (∑ i ∈ range na, A i * (x - p) ^ i) *
      (∑ j ∈ range nb, B j * (x - p) ^ j) * (∑ l ∈ range nc, C l * (x - p) ^ l))
      = ∫ x in p..q, (∑ l ∈ range nc, ∑ j ∈ range nb, ∑ i ∈ range na,
          A i * B j * C l * (x - p) ^ (i + j + l)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact poly3_eq p x A B C na nb nc
  rw [hcongr, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [intervalIntegral.integral_const_mul, int_pow_sub]
        push_cast
        ring
      · intro i _
        exact (by fun_prop : Continuous fun x : ℝ => A i * B j * C l * (x - p) ^ (i + j + l)).intervalIntegrable _ _
    · intro j _
      exact (by fun_prop : Continuous fun x : ℝ => ∑ i ∈ range na, A i * B j * C l * (x - p) ^ (i + j + l)).intervalIntegrable _ _
  · intro l _
    exact (by fun_prop : Continuous fun x : ℝ => ∑ j ∈ range nb, ∑ i ∈ range na,
      A i * B j * C l * (x - p) ^ (i + j + l)).intervalIntegrable _ _


/-! ### Three elementary estimates used for the positivity of the bounds -/

private lemma alt8_ge {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    u - u ^ 2 / 2 ≤ ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
  have hexp : (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1))
      = u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5 - u ^ 6 / 6 + u ^ 7 / 7 - u ^ 8 / 8 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  rw [hexp]
  have h3 : 0 ≤ u ^ 3 * (1 / 3 - u / 4) := mul_nonneg (pow_nonneg h0 3) (by linarith)
  have h5 : 0 ≤ u ^ 5 * (1 / 5 - u / 6) := mul_nonneg (pow_nonneg h0 5) (by linarith)
  have h7 : 0 ≤ u ^ 7 * (1 / 7 - u / 8) := mul_nonneg (pow_nonneg h0 7) (by linarith)
  nlinarith [h3, h5, h7]

private lemma two_u9_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : 2 * u ^ 9 ≤ u - u ^ 2 / 2 := by
  have h3 : 2 * u ^ 9 ≤ u / 128 := by
    have h2 : u ^ 8 ≤ (1 / 2 : ℝ) ^ 8 := pow_le_pow_left₀ h0 h1 8
    nlinarith [pow_nonneg h0 9]
  nlinarith

private lemma geom9_ge {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1 / 2) :
    1 / 2 ≤ ∑ l ∈ range 9, (-w) ^ l := by
  have hexp : (∑ l ∈ range 9, (-w) ^ l)
      = 1 - w + w ^ 2 - w ^ 3 + w ^ 4 - w ^ 5 + w ^ 6 - w ^ 7 + w ^ 8 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hexp]
  have hg : 1 - w + w ^ 2 - w ^ 3 + w ^ 4 - w ^ 5 + w ^ 6 - w ^ 7 + w ^ 8
      = (1 - w) * (1 + w ^ 2 + w ^ 4 + w ^ 6) + w ^ 8 := by ring
  rw [hg]
  have hpos : 0 ≤ (1 - w) * (1 + w ^ 2 + w ^ 4 + w ^ 6) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [pow_nonneg h0 8]

/-! ### The panel lower bound for `∫ log (x-1) log (5/(x+1)) / x` -/

private lemma P_panel_lower (p q : ℚ) (hp : 2 ≤ p) (hq : q ≤ 4) (hpq : p < q)
    (hsmall : q - p ≤ (p - 1) / 2) (hsmall2 : q - p ≤ p / 2)
    (lL lG : ℚ)
    (hlL : (lL : ℝ) ≤ Real.log ((p : ℝ) - 1)) (hlL0 : 0 ≤ (lL : ℝ))
    (hlG : (lG : ℝ) ≤ Real.log (5 / ((p : ℝ) + 1))) :
    (∑ l ∈ range 9, ∑ j ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lL else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else -2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j = 0 then lG else if j ≤ 8 then -((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j)
              else -2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p - ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j + l + 1) / ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)))
      ≤ ∫ x in (p : ℝ)..(q : ℝ), Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hQ4 : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hP1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hPQ : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hH0 : (0 : ℝ) ≤ (q : ℝ) - (p : ℝ) := by linarith
  have hs1 : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ (((p - 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall
    push_cast at this ⊢
    linarith
  have hs2 : (q : ℝ) - (p : ℝ) ≤ (p : ℝ) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ ((p / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall2
    push_cast at this ⊢
    linarith
  set A : ℕ → ℝ := fun i => (((if i = 0 then lL else if i ≤ 8 then
      (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i) else -2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
    with hAdef
  set B : ℕ → ℝ := fun j => (((if j = 0 then lG else if j ≤ 8 then
      -((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j) else -2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ)
    with hBdef
  set C : ℕ → ℝ := fun l => (((if l = 0 then
      (1 : ℚ) / p - ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
      else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ) with hCdef
  have hrow : (∑ l ∈ range 9, ∑ j ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lL else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else -2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j = 0 then lG else if j ≤ 8 then -((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j)
              else -2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p - ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j + l + 1) / ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range 9, ∑ j ∈ range 10, ∑ i ∈ range 10,
          A i * B j * C l * (((q : ℝ) - (p : ℝ)) ^ (i + j + l + 1) / ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAdef, hBdef, hCdef]
  rw [hrow, ← int_prod3 (p : ℝ) (q : ℝ) hPQ.le A B C 10 10 9]
  refine intervalIntegral.integral_mono_on hPQ.le ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
        (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)).intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hPQ.le]
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact ContinuousOn.log (by fun_prop) (fun x hx => by linarith [hx.1])
      · apply ContinuousOn.log ?_ (fun x hx =>
          ne_of_gt (div_pos (by norm_num) (by linarith [hx.1])))
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro x hx
        linarith [hx.1]
    · exact continuousOn_id
    · intro x hx
      change x ≠ 0
      linarith [hx.1]
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (p : ℝ) with htdef
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htH : t ≤ (q : ℝ) - (p : ℝ) := by rw [htdef]; linarith
    have hP0' : (0 : ℝ) < (p : ℝ) := hP0
    have hPm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hPp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    set u : ℝ := t / ((p : ℝ) - 1) with hudef
    set v : ℝ := t / ((p : ℝ) + 1) with hvdef
    set w : ℝ := t / (p : ℝ) with hwdef
    have hu0 : 0 ≤ u := div_nonneg ht0 hPm1.le
    have hu1 : u ≤ 1 / 2 := by
      rw [hudef, div_le_iff₀ hPm1]
      have hHle : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := hs1
      nlinarith
    have hv0 : 0 ≤ v := div_nonneg ht0 hPp1.le
    have hv1 : v ≤ 1 / 2 := by
      rw [hvdef, div_le_iff₀ hPp1]
      nlinarith [hs2, htH]
    have hw0 : 0 ≤ w := div_nonneg ht0 hP0.le
    have hw1 : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ hP0]
      nlinarith [hs2, htH]
    have hu_pos : (0 : ℝ) < 1 + u := by linarith
    have hv_pos : (0 : ℝ) < 1 + v := by linarith
    -- the coefficient identities
    have eA0 : A 0 = (lL : ℝ) := by
      simp only [hAdef, ↓reduceIte]
    have eA9 : A 9 = -2 / ((p : ℝ) - 1) ^ 9 := by
      simp only [hAdef]
      rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
      push_cast
      ring
    have eB0 : B 0 = (lG : ℝ) := by
      simp only [hBdef, ↓reduceIte]
    have eB9 : B 9 = -2 / ((p : ℝ) + 1) ^ 9 := by
      simp only [hBdef]
      rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
      push_cast
      ring
    have hArow : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i)
        = (lL : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) - 2 * u ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ, eA0, eA9]
      have hmid : (∑ i ∈ range 8, A (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hAi : A (i + 1) = (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) - 1) ^ (i + 1) := by
          simp only [hAdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hAi]
        rw [show u ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) - 1) ^ (i + 1) from by
          rw [hudef, div_pow]]
        ring
      rw [hmid]
      rw [show -2 / ((p : ℝ) - 1) ^ 9 * (x - (p : ℝ)) ^ 9 = -(2 * u ^ 9) from by
        rw [show u ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) - 1) ^ 9 from by rw [hudef, div_pow]]
        field_simp]
      ring
    have hBrow : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
        = (lG : ℝ) - (∑ j ∈ range 8, (-1 : ℝ) ^ j * v ^ (j + 1) / (j + 1)) - 2 * v ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ, eB0, eB9]
      have hmid : (∑ j ∈ range 8, B (j + 1) * (x - (p : ℝ)) ^ (j + 1))
          = ∑ j ∈ range 8, -((-1 : ℝ) ^ j * v ^ (j + 1) / (j + 1)) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj8 : j + 1 ≤ 8 := by simpa using Finset.mem_range.mp hj
        have hBj : B (j + 1) = -((-1 : ℝ) ^ j) / ((j : ℝ) + 1) / ((p : ℝ) + 1) ^ (j + 1) := by
          simp only [hBdef]
          rw [if_neg (by omega : j + 1 ≠ 0), if_pos hj8]
          push_cast
          field_simp
        rw [hBj]
        rw [show v ^ (j + 1) = (x - (p : ℝ)) ^ (j + 1) / ((p : ℝ) + 1) ^ (j + 1) from by
          rw [hvdef, div_pow]]
        ring
      rw [hmid, Finset.sum_neg_distrib]
      rw [show -2 / ((p : ℝ) + 1) ^ 9 * (x - (p : ℝ)) ^ 9 = -(2 * v ^ 9) from by
        rw [show v ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) + 1) ^ 9 from by rw [hvdef, div_pow]]
        field_simp]
      ring
    have hCrow : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
        = (1 / (p : ℝ) - (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
          + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
      rw [Finset.sum_range_succ']
      have eC0 : C 0 = (1 / (p : ℝ) - (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
        simp only [hCdef]
        push_cast
        rw [mul_div_assoc]
      rw [eC0]
      have hmid : (∑ l ∈ range 8, C (l + 1) * (x - (p : ℝ)) ^ (l + 1))
          = (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hCl : C (l + 1) = (-1 : ℝ) ^ (l + 1) / (p : ℝ) ^ (l + 2) := by
          simp only [hCdef]
          rw [if_neg (by omega : l + 1 ≠ 0)]
          push_cast
          field_simp
        rw [hCl]
        rw [show (-w) ^ (l + 1) = (-1 : ℝ) ^ (l + 1) * (x - (p : ℝ)) ^ (l + 1) / (p : ℝ) ^ (l + 1) from by
          rw [hwdef, show -(t / (p:ℝ)) = -((x - (p:ℝ)) / (p:ℝ)) from by rw [htdef], neg_pow, div_pow]
          ring]
        field_simp
        rw [pow_succ]
        ring
      rw [hmid]
      ring
    -- bounds for the three factors
    have hAle : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) ≤ Real.log (x - 1) := by
      rw [hArow]
      have hx1 : x - 1 = ((p : ℝ) - 1) * (1 + u) := by
        rw [show 1 + u = (x - 1) / ((p : ℝ) - 1) from by
          rw [hudef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_mul (by linarith) (by linarith)]
      have h := log_one_add_ge9 hu0 hu1
      have h1 := add_le_add hlL h
      calc (lL : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) - 2 * u ^ 9
          = (lL : ℝ) + ((∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) - 2 * u ^ 9) := by
            ring
        _ ≤ Real.log ((p : ℝ) - 1) + Real.log (1 + u) := h1
    have hBle : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) ≤ Real.log (5 / (x + 1)) := by
      rw [hBrow]
      have hx1 : 5 / (x + 1) = (5 / ((p : ℝ) + 1)) / (1 + v) := by
        rw [show 1 + v = (x + 1) / ((p : ℝ) + 1) from by
          rw [hvdef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_div (by positivity) (by linarith)]
      have h := log_one_add_le9 hv0 hv1
      calc (lG : ℝ) - (∑ j ∈ range 8, (-1 : ℝ) ^ j * v ^ (j + 1) / (j + 1)) - 2 * v ^ 9
          = (lG : ℝ) + (-(∑ j ∈ range 8, (-1 : ℝ) ^ j * v ^ (j + 1) / (j + 1)) - 2 * v ^ 9) := by
            ring
        _ ≤ Real.log (5 / ((p : ℝ) + 1)) + (-Real.log (1 + v)) := by linarith [h, hlG]
    have hCle : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≤ 1 / x := by
      rw [hCrow]
      have hsum : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := (inv_geom_bounds (p := (p : ℝ)) (h := (q : ℝ) - (p : ℝ)) hP0 hH0 hs2 8
        (t := t) ⟨ht0, htH⟩).1
      rw [show -(t / (p : ℝ)) = -w from by rw [hwdef]] at hg
      rw [show (p : ℝ) + t = x from by rw [htdef]; ring, hsum] at hg
      calc (1 / (p : ℝ) - (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 + ∑ l ∈ range 8, (-w) ^ (l + 1)) * (1 / (p : ℝ))
            - (1 / (p : ℝ)) * ((((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
            rw [show (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) = (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 from by norm_num]
            ring
        _ ≤ 1 / x := hg
    -- positivity of two of them
    have hA0 : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) := by
      rw [hArow]
      have h1 := alt8_ge hu0 hu1
      have h2 := two_u9_le hu0 hu1
      nlinarith [hlL0]
    have hC0 : 0 ≤ (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by
      rw [hCrow]
      have hsum9 : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := geom9_ge hw0 hw1
      rw [hsum9] at hg
      have hrat : (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 / (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)) ≤ 1 / 2 := by
        have h0 : 0 ≤ ((q : ℝ) - (p : ℝ)) / (p : ℝ) := div_nonneg hH0 hP0.le
        have h1 : ((q : ℝ) - (p : ℝ)) / (p : ℝ) ≤ 1 / 2 := by
          rw [div_le_iff₀ hP0]; linarith
        have h2 : (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 ≤ (1 / 2 : ℝ) ^ 9 :=
          pow_le_pow_left₀ h0 h1 9
        have h3 : (0 : ℝ) < 1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ) := by linarith
        rw [div_le_iff₀ h3]
        nlinarith [pow_nonneg h0 9]
      have hinv : (0 : ℝ) < 1 / (p : ℝ) := by positivity
      have hX1 : (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 / (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)) ≤ 1 := by
        linarith [hrat]
      have hS2 : -(1 / 2 : ℝ) ≤ ∑ l ∈ range 8, (-w) ^ (l + 1) := by linarith [hg]
      have e1 : (1 / (p : ℝ) - (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 / (p : ℝ)) * (1 - (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)) + ∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        ring
      rw [e1]
      apply mul_nonneg hinv.le
      linarith
    -- the product comparison
    have hf0 : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
    have hg0 : 0 ≤ Real.log (5 / (x + 1)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hxpos : (0 : ℝ) < x := by linarith
    by_cases hB : 0 ≤ (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
    · have h1 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
          (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          ≤ Real.log (x - 1) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) :=
        mul_le_mul_of_nonneg_right hAle hB
      have h2 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
            (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
          ≤ Real.log (x - 1) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
        mul_le_mul_of_nonneg_right h1 hC0
      have h3 : Real.log (x - 1) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          ≤ Real.log (x - 1) * Real.log (5 / (x + 1)) :=
        mul_le_mul_of_nonneg_left hBle hf0
      have h4 : Real.log (x - 1) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
          ≤ Real.log (x - 1) * Real.log (5 / (x + 1)) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
        mul_le_mul_of_nonneg_right h3 hC0
      have h5 : Real.log (x - 1) * Real.log (5 / (x + 1)) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
          ≤ Real.log (x - 1) * Real.log (5 / (x + 1)) * (1 / x) :=
        mul_le_mul_of_nonneg_left hCle (mul_nonneg hf0 hg0)
      have h6 : Real.log (x - 1) * Real.log (5 / (x + 1)) * (1 / x)
          = Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
        simp only [div_eq_mul_inv]
        ring
      linarith [h2, h4, h5]
    · have hBlt : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) < 0 := not_le.mp hB
      have hAC : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
          (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := mul_nonneg hA0 hC0
      have hzero : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
            (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≤ 0 := by
        nlinarith
      have hpos : 0 ≤ Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by positivity
      linarith

/-! ### The F0 leaf -/

private lemma logLowerQ_nonneg (N : ℕ) (y : ℚ) (hy : 1 ≤ y) :
    (0 : ℚ) ≤ 2 * ∑ j ∈ range N, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1) := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  apply div_nonneg
  · apply pow_nonneg
    apply div_nonneg <;> linarith
  · positivity

/-! ### Integrability and continuity of the inner primitive in `F0` -/

private lemma logquot_continuousOn :
    ContinuousOn (fun x : ℝ => Real.log (x - 1) / x) (Set.uIcc (2:ℝ) 4) := by
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
  apply ContinuousOn.div
  · apply ContinuousOn.log (by fun_prop)
    intro x hx; linarith [hx.1]
  · exact continuousOn_id
  · intro x hx; change x ≠ 0; linarith [hx.1]

private lemma logquot_integrable : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume 2 4 :=
  logquot_continuousOn.intervalIntegrable

private lemma inner_cont :
    ContinuousOn (fun t : ℝ => ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) (Set.uIcc (4:ℝ) 6) := by
  have h := continuousOn_primitive_interval' logquot_integrable
    (Set.left_mem_uIcc (a := (2:ℝ)) (b := (4:ℝ)))
  refine h.comp (by fun_prop) ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 6)] at ht
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
  constructor <;> linarith [ht.1, ht.2]

private lemma inner_split_integrable :
    IntervalIntegrable (fun t : ℝ => (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) / (t - 1))
      volume 4 6 := by
  have hcont : ContinuousOn
      (fun t : ℝ => (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) / (t - 1)) (Set.uIcc 4 6) := by
    refine ContinuousOn.div inner_cont ?_ ?_
    · exact (by fun_prop : ContinuousOn (fun t : ℝ => t - 1) (Set.uIcc (4:ℝ) 6))
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 6)] at ht
      change t - 1 ≠ 0
      linarith [ht.1]
  exact hcont.intervalIntegrable

private lemma logP_continuousOn {u v : ℝ} (huv : u ≤ v) (hu : 2 ≤ u) :
    ContinuousOn (fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · apply ContinuousOn.log (by fun_prop)
      intro x hx; linarith [hx.1]
    · apply ContinuousOn.log ?_ (fun x hx => ne_of_gt (div_pos (by norm_num) (by linarith [hx.1])))
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; linarith [hx.1]
  · exact continuousOn_id
  · intro x hx
    change x ≠ 0
    linarith [hx.1]

/-! ### The 16-panel lower bound for `∫_2^4 log (x-1) log (5/(x+1)) / x` -/

private lemma P_partition_lower :
    (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
      (((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i) : ℚ) : ℝ)
      * (((if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j') : ℚ) : ℝ)
      * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ)
      * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) /
          ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)))
    ≤ ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
  set a : ℕ → ℝ := fun j => ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) with hadef
  have ha0 : a 0 = 2 := by
    rw [hadef]; norm_num
  have ha16 : a 16 = 4 := by
    rw [hadef]; norm_num
  have hadj : ∀ j : ℕ, a (j + 1) - a j = 2 / 16 := by
    intro j
    rw [hadef]
    push_cast
    ring
  have hint : ∀ k < 16, IntervalIntegrable
      (fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ a k := by
      rw [hadef]
      push_cast
      have h : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hle : a k ≤ a (k + 1) := by
      rw [hadef]
      push_cast
      have h : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
      linarith
    exact (logP_continuousOn hle hk2).intervalIntegrable
  have hcell : ∀ j ∈ range 16,
      (∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then (2 * ∑ k ∈ range 20,
              (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
                (2 * k + 1))
            else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
            else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then (2 * ∑ k ∈ range 20,
              (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
                (2 * k + 1))
            else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
            else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
                ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                  ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                    (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
            else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) /
            ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)))
      ≤ ∫ x in a j..a (j + 1), Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
    intro j hj
    have hj16 : j < 16 := Finset.mem_range.mp hj
    have hj0 : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
    have hp2 : (2 : ℚ) ≤ 2 + 2 * (j : ℚ) / 16 := by
      have h : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
      linarith
    have hq4 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 ≤ 4 := by
      have hj1 : ((j + 1 : ℕ) : ℚ) ≤ 16 := by
        have h : j + 1 ≤ 16 := by omega
        exact_mod_cast h
      nlinarith
    have hpq : 2 + 2 * (j : ℚ) / 16 < 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 := by
      have h : (j : ℚ) < ((j + 1 : ℕ) : ℚ) := by
        have h' : j < j + 1 := by omega
        exact_mod_cast h'
      linarith
    have hsmall : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) ≤
        (2 + 2 * (j : ℚ) / 16 - 1) / 2 := by
      have h1 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) = 2 / 16 := by
        push_cast
        ring
      rw [h1]
      nlinarith
    have hsmall2 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) ≤
        (2 + 2 * (j : ℚ) / 16) / 2 := by
      have h1 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) = 2 / 16 := by
        push_cast
        ring
      rw [h1]
      nlinarith
    have hy1 : (1 : ℚ) ≤ 2 + 2 * (j : ℚ) / 16 - 1 := by
      have h : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
      linarith
    have hyL : (1 : ℝ) ≤ ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ) := by exact_mod_cast hy1
    have hy1G : (1 : ℚ) ≤ 5 / (2 + 2 * (j : ℚ) / 16 + 1) := by
      rw [le_div_iff₀ (by positivity)]
      have h : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
      linarith
    have hyG : (1 : ℝ) ≤ ((5 / (2 + 2 * (j : ℚ) / 16 + 1) : ℚ) : ℝ) := by exact_mod_cast hy1G
    have hlL : ((2 * ∑ k ∈ range 20,
          (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
            (2 * k + 1) : ℚ) : ℝ) ≤ Real.log (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) - 1) := by
      have hc := rat_logLower_cast' 20 (2 + 2 * (j : ℚ) / 16 - 1)
      have hb := (Wu04Integral.log_bounds 20 (y := ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ)) hyL).1
      have hcast : ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ) = ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) - 1 := by
        push_cast
        ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hlL0 : (0 : ℝ) ≤ ((2 * ∑ k ∈ range 20,
          (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
            (2 * k + 1) : ℚ) : ℝ) := by
      have h := logLowerQ_nonneg 20 (2 + 2 * (j : ℚ) / 16 - 1) hy1
      exact_mod_cast h
    have hlG : ((2 * ∑ k ∈ range 20,
          (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
            (2 * k + 1) : ℚ) : ℝ) ≤ Real.log (5 / (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) + 1)) := by
      have hc := rat_logLower_cast' 20 (5 / (2 + 2 * (j : ℚ) / 16 + 1))
      have hb := (Wu04Integral.log_bounds 20 (y := ((5 / (2 + 2 * (j : ℚ) / 16 + 1) : ℚ) : ℝ)) hyG).1
      have hcast : ((5 / (2 + 2 * (j : ℚ) / 16 + 1) : ℚ) : ℝ) =
          (5 : ℝ) / (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) + 1) := by
        push_cast
        ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hpanel := P_panel_lower (p := 2 + 2 * (j : ℚ) / 16)
      (q := 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16)
      (lL := 2 * ∑ k ∈ range 20,
        (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1))
      (lG := 2 * ∑ k ∈ range 20,
        (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1))
      hp2 hq4 hpq hsmall hsmall2 hlL hlL0 hlG
    have hcast2 : ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) = a j := by rw [hadef]
    have hcast3 : ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) = a (j + 1) := by
      rw [hadef]
    simpa only [hcast2, hcast3] using hpanel
  have hsum_int : (∑ j ∈ range 16, ∫ x in a j..a (j + 1),
      Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
      = ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
    have h := sum_integral_adjacent_intervals (a := a) (n := 16)
      (f := fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) hint
    rw [ha0, ha16] at h
    exact h
  rw [← hsum_int]
  exact Finset.sum_le_sum hcell

/-! ### The inner-integral identity of `F0` -/

private lemma one_div_sub_one_int :
    (∫ t in (4:ℝ)..6, 1 / (t - 1)) = Real.log (5 / 3) := by
  have h := intervalIntegral.integral_comp_sub_right (a := (4:ℝ)) (b := 6) (fun u : ℝ => (u)⁻¹) 1
  rw [show (4:ℝ) - 1 = 3 by norm_num, show (6:ℝ) - 1 = 5 by norm_num] at h
  rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 5)] at h
  simpa only [one_div] using h

private lemma one_div_sub_one_integrable : IntervalIntegrable (fun t : ℝ => 1 / (t - 1)) volume 4 6 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 6)]
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro t ht
  change t - 1 ≠ 0
  linarith [ht.1]

private lemma weight_integral : ∀ x ∈ Set.uIcc (2:ℝ) 4,
    (∫ t in (x + 2)..6, 1 / (t - 1)) = Real.log (5 / (x + 1)) := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
  have h := intervalIntegral.integral_comp_sub_right (a := x + 2) (b := 6) (fun u : ℝ => (u)⁻¹) 1
  rw [show x + 2 - 1 = x + 1 by ring, show (6:ℝ) - 1 = 5 by norm_num] at h
  rw [integral_inv_of_pos (by linarith [hx.1] : (0:ℝ) < x + 1) (by norm_num : (0:ℝ) < 5)] at h
  simpa only [one_div] using h

private lemma F0_inner_identity :
    (∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)))
      = Real.log (5 / 3) + ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
  have hint2 : IntervalIntegrable
      (fun t : ℝ => (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1))) volume 4 6 := by
    simpa only [div_eq_mul_inv, one_mul] using inner_split_integrable
  have hsplit : (∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)))
      = (∫ t in (4:ℝ)..6, 1 / (t - 1))
        + ∫ t in (4:ℝ)..6, (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)) := by
    rw [← intervalIntegral.integral_add one_div_sub_one_integrable hint2]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hswap := triangle_swap (f := fun x : ℝ => Real.log (x - 1) / x) (h := fun t : ℝ => 1 / (t - 1))
    (c := 2) (A := 4) (B := 6) (hc := by norm_num) (hAB := by norm_num)
    (hf := by
      rw [show (4:ℝ) - 2 = 2 by norm_num, show (6:ℝ) - 2 = 4 by norm_num]
      exact logquot_continuousOn)
    (hh := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 6)] at ht
      change t - 1 ≠ 0
      linarith [ht.1])
  simp only [show (4:ℝ) - 2 = 2 by norm_num, show (6:ℝ) - 2 = 4 by norm_num] at hswap
  calc (∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)))
      = (∫ t in (4:ℝ)..6, 1 / (t - 1))
        + ∫ t in (4:ℝ)..6, (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)) := hsplit
    _ = Real.log (5 / 3)
        + ∫ t in (4:ℝ)..6, (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)) := by
        rw [one_div_sub_one_int]
    _ = Real.log (5 / 3) + ∫ x in (2:ℝ)..4,
          Real.log (x - 1) / x * (∫ t in (x + 2)..6, 1 / (t - 1)) := by
        rw [hswap]
    _ = Real.log (5 / 3) + ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x hx
        change Real.log (x - 1) / x * (∫ t in (x + 2)..6, 1 / (t - 1))
          = Real.log (x - 1) * Real.log (5 / (x + 1)) / x
        rw [weight_integral x hx]
        ring

private theorem certQ :
    (13473613 / 1000000 : ℚ) ≤ 8 * ((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + (2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1))) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) := by
  decide +kernel

private lemma certQR :
    ((13473613 / 1000000 : ℚ) : ℝ) ≤ ((8 * ((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + (2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1))) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) : ℚ) : ℝ) := by
  exact_mod_cast certQ

private lemma castsplit :
    ((8 * ((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + (2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1))) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) : ℚ) : ℝ) =
      8 * (((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) : ℚ) : ℝ) + 8 * (((2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) : ℚ) : ℝ)
      + 8 * (((∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) : ℚ) : ℝ) := by
  push_cast
  ring

private lemma castsum :
    (((∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) : ℚ) : ℝ) =
      (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
      (((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i) : ℚ) : ℝ)
      * (((if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j') : ℚ) : ℝ)
      * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ)
      * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) /
          ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1))) := by
  push_cast
  ring

/-- LEAF. Wu 2004 page 42 final numerical display, F0.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F0 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    13.473613 ≤ integralTerms F f ω 0 := by

  have hF0 := Task275.F0_elementary (F := F) (f := f) h ω
  rw [hF0]
  have hform : (∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 1 - 1), Real.log (x - 1) / x) / (t - 1))
      = ∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    show (1 + ∫ x in (2:ℝ)..(t - 1 - 1), Real.log (x - 1) / x) / (t - 1)
      = (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1))
    rw [show (t - 1 - 1 : ℝ) = t - 2 by ring]
    ring
  rw [hform, F0_inner_identity]
  -- logarithm bounds for the two constants
  have h3 : (((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) : ℚ) : ℝ)
      ≤ Real.log 3 := by
    have hc := rat_logLower_cast' 20 (3 : ℚ)
    have hb := (Wu04Integral.log_bounds 20 (y := ((3 : ℚ) : ℝ)) (by norm_num)).1
    have hcast : ((3 : ℚ) : ℝ) = (3 : ℝ) := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have h53 : (((2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) : ℚ) : ℝ)
      ≤ Real.log (5 / 3) := by
    have hc := rat_logLower_cast' 20 (5 / 3 : ℚ)
    have hb := (Wu04Integral.log_bounds 20 (y := ((5 / 3 : ℚ) : ℝ)) (by norm_num)).1
    have hcast : ((5 / 3 : ℚ) : ℝ) = (5 : ℝ) / 3 := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  -- assemble: the certificate cast to the reals, then the panel bound
  have hc := certQR
  rw [castsplit, castsum] at hc
  have hP := P_partition_lower
  have hmain : ((13473613 / 1000000 : ℚ) : ℝ) ≤
      8 * (Real.log 3 + (Real.log (5 / 3) + ∫ x in (2:ℝ)..4,
        Real.log (x - 1) * Real.log (5 / (x + 1)) / x)) := by
    nlinarith [hc, h3, h53, hP]
  calc (13.473613 : ℝ) = ((13473613 / 1000000 : ℚ) : ℝ) := by norm_num
    _ ≤ 8 * (Real.log 3 + (Real.log (5 / 3) + ∫ x in (2:ℝ)..4,
        Real.log (x - 1) * Real.log (5 / (x + 1)) / x)) := hmain

private lemma tail_weight_cont : ContinuousOn (fun t : ℝ => 1 / (t * (1 - t / 6))) (Set.uIcc (3:ℝ) 5) := by
  rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)]
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro t ht
    have h1 : t ≠ 0 := by linarith [ht.1]
    have h2 : (1 : ℝ) - t / 6 ≠ 0 := by linarith [ht.2]
    exact mul_ne_zero h1 h2

private lemma split_one_div {t : ℝ} (ht : t ≠ 0) (h6 : 6 - t ≠ 0) :
    1 / (t * (1 - t / 6)) = 1 / t + 1 / (6 - t) := by
  have h1 : (1 : ℝ) - t / 6 ≠ 0 := by
    intro hc
    apply h6
    field_simp at hc
    linarith
  rw [show t * (1 - t / 6) = t * (6 - t) / 6 by ring]
  field_simp
  ring

private lemma tail_weight_int : (∫ t in (3:ℝ)..5, 1 / (t * (1 - t / 6))) = Real.log 5 := by
  have he : (∫ t in (3:ℝ)..5, 1 / (t * (1 - t / 6)))
      = ∫ t in (3:ℝ)..5, (1 / t + 1 / (6 - t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)] at ht
    exact split_one_div (by linarith [ht.1]) (by linarith [ht.2])
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; change t ≠ 0; linarith [ht.1]
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / (6 - t)) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; change 6 - t ≠ 0; linarith [ht.2]
  rw [he, intervalIntegral.integral_add hi1 hi2]
  have h1 : (∫ t in (3:ℝ)..5, 1 / t) = Real.log (5 / 3) := by
    rw [show (∫ t in (3:ℝ)..5, 1 / t) = ∫ t in (3:ℝ)..5, (t)⁻¹ from by
      apply intervalIntegral.integral_congr; intro t _; rw [one_div]]
    rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 5)]
  have h2 : (∫ t in (3:ℝ)..5, 1 / (6 - t)) = Real.log 3 := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun u : ℝ => (u)⁻¹) 6
      (a := (3:ℝ)) (b := 5)
    rw [show (6:ℝ) - 5 = 1 by norm_num, show (6:ℝ) - 3 = 3 by norm_num] at hcomp
    rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 3)] at hcomp
    rw [show (∫ t in (3:ℝ)..5, 1 / (6 - t)) = ∫ t in (3:ℝ)..5, ((fun u : ℝ => (u)⁻¹) (6 - t)) from by
      apply intervalIntegral.integral_congr; intro t _; simp only [one_div]]
    rw [hcomp]
    norm_num
  rw [h1, h2]
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

private lemma tail_weight_point : ∀ x ∈ Set.uIcc (2:ℝ) 4,
    (∫ t in (x + 1)..5, 1 / (t * (1 - t / 6))) = Real.log (5 * (5 - x) / (x + 1)) := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
  have hx1 : (0:ℝ) < x + 1 := by linarith [hx.1]
  have hx5 : (0:ℝ) < 5 - x := by linarith [hx.2]
  have hupper : x + 1 ≤ 5 := by linarith [hx.2]
  have he : (∫ t in (x + 1)..5, 1 / (t * (1 - t / 6)))
      = ∫ t in (x + 1)..5, (1 / t + 1 / (6 - t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hupper] at ht
    exact split_one_div (by linarith [ht.1]) (by linarith [ht.2])
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (x + 1) 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hupper]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; change t ≠ 0; linarith [ht.1]
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / (6 - t)) volume (x + 1) 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hupper]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; change 6 - t ≠ 0; linarith [ht.2]
  rw [he, intervalIntegral.integral_add hi1 hi2]
  have h1 : (∫ t in (x + 1)..5, 1 / t) = Real.log (5 / (x + 1)) := by
    rw [show (∫ t in (x + 1)..5, 1 / t) = ∫ t in (x + 1)..5, (t)⁻¹ from by
      apply intervalIntegral.integral_congr; intro t _; rw [one_div]]
    rw [integral_inv_of_pos hx1 (by norm_num : (0:ℝ) < 5)]
  have h2 : (∫ t in (x + 1)..5, 1 / (6 - t)) = Real.log (5 - x) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun u : ℝ => (u)⁻¹) 6
      (a := x + 1) (b := 5)
    rw [show (6:ℝ) - 5 = 1 by norm_num, show (6:ℝ) - (x + 1) = 5 - x by ring] at hcomp
    rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 1) hx5] at hcomp
    rw [show (∫ t in (x + 1)..5, 1 / (6 - t)) = ∫ t in (x + 1)..5, ((fun u : ℝ => (u)⁻¹) (6 - t)) from by
      apply intervalIntegral.integral_congr; intro t _; simp only [one_div]]
    rw [hcomp]
    rw [show (5 - x) / 1 = 5 - x by norm_num]
  rw [h1, h2]
  rw [← Real.log_mul (by positivity) hx5.ne']
  congr 1
  field_simp

private lemma inner_cont3 :
    ContinuousOn (fun t : ℝ => ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) (Set.uIcc (3:ℝ) 5) := by
  have h := continuousOn_primitive_interval' logquot_integrable
    (Set.left_mem_uIcc (a := (2:ℝ)) (b := (4:ℝ)))
  refine h.comp (by fun_prop) ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)] at ht
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
  constructor <;> linarith [ht.1, ht.2]

private lemma F3_inner_identity :
    (∫ t in (3:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / (t * (1 - t / 6))))
      = Real.log 5 + ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x := by
  have hint2 : IntervalIntegrable
      (fun t : ℝ => (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / (t * (1 - t / 6))))
      volume 3 5 := by
    have hcont : ContinuousOn
        (fun t : ℝ => (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / (t * (1 - t / 6))))
        (Set.uIcc (3:ℝ) 5) := by
      refine ContinuousOn.mul inner_cont3 ?_
      exact (tail_weight_cont.mono (by intro t ht; exact ht))
    exact hcont.intervalIntegrable
  have hsplit : (∫ t in (3:ℝ)..5,
        (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / (t * (1 - t / 6))))
      = (∫ t in (3:ℝ)..5, 1 / (t * (1 - t / 6)))
        + ∫ t in (3:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
            (1 / (t * (1 - t / 6))) := by
    rw [← intervalIntegral.integral_add tail_weight_cont.intervalIntegrable hint2]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hswap := triangle_swap (f := fun x : ℝ => Real.log (x - 1) / x)
    (h := fun t : ℝ => 1 / (t * (1 - t / 6))) (c := 1) (A := 3) (B := 5)
    (hc := by norm_num) (hAB := by norm_num)
    (hf := by
      rw [show (3:ℝ) - 1 = 2 by norm_num, show (5:ℝ) - 1 = 4 by norm_num]
      exact logquot_continuousOn)
    (hh := by
      rw [show (3:ℝ) = 3 by norm_num]
      exact tail_weight_cont)
  simp only [show (3:ℝ) - 1 = 2 by norm_num, show (5:ℝ) - 1 = 4 by norm_num] at hswap
  calc (∫ t in (3:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
        (1 / (t * (1 - t / 6))))
      = (∫ t in (3:ℝ)..5, 1 / (t * (1 - t / 6)))
        + ∫ t in (3:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
            (1 / (t * (1 - t / 6))) := hsplit
    _ = Real.log 5 + ∫ t in (3:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
            (1 / (t * (1 - t / 6))) := by rw [tail_weight_int]
    _ = Real.log 5 + ∫ x in (2:ℝ)..4,
          Real.log (x - 1) / x * (∫ t in (x + 1)..5, 1 / (t * (1 - t / 6))) := by
        rw [hswap]
    _ = Real.log 5 + ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x hx
        change Real.log (x - 1) / x * (∫ t in (x + 1)..5, 1 / (t * (1 - t / 6)))
          = Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x
        rw [tail_weight_point x hx]
        ring

private lemma logQD_continuousOn {u v : ℝ} (huv : u ≤ v) (hu : 2 ≤ u) (hv : v ≤ 4) :
    ContinuousOn (fun x : ℝ => Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · apply ContinuousOn.log (by fun_prop)
      intro x hx; linarith [hx.1]
    · apply ContinuousOn.log ?_ (fun x hx => ne_of_gt (div_pos (by nlinarith [hx.2]) (by linarith [hx.1])))
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx; linarith [hx.1]
  · exact continuousOn_id
  · intro x hx
    change x ≠ 0
    linarith [hx.1]

/-! ### The panel upper bound for `∫ log (x-1) log (5(5-x)/(x+1)) / x` -/

private lemma Q_panel_upper (p q : ℚ) (hp : 2 ≤ p) (hq : q ≤ 4) (hpq : p < q)
    (hsmall : q - p ≤ (p - 1) / 2) (hsmall2 : q - p ≤ p / 2)
    (lU gU : ℚ)
    (hlU : Real.log ((p : ℝ) - 1) ≤ (lU : ℝ))
    (hlG : Real.log (5 * (5 - (p : ℝ)) / ((p : ℝ) + 1)) ≤ (gU : ℝ)) :
    (∫ x in (p : ℝ)..(q : ℝ),
        Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      ≤ ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then gU else if j' ≤ 8 then
              -((1 : ℚ) / ((j' : ℚ) * ((5 - p : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((p + 1 : ℚ)) ^ j')
              else 2 / ((5 - p : ℚ)) ^ j' + 2 / ((p + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hP1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hPQ : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hQ4 : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hs1 : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ (((p - 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall
    push_cast at this ⊢
    linarith
  have hs2 : (q : ℝ) - (p : ℝ) ≤ (p : ℝ) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ ((p / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall2
    push_cast at this ⊢
    linarith
  set A : ℕ → ℝ := fun i => (((if i = 0 then lU else if i ≤ 8 then
      (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i) else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
    with hAdef
  set B : ℕ → ℝ := fun j => (((if j = 0 then gU else if j ≤ 8 then
      -((1 : ℚ) / ((j : ℚ) * ((5 - p : ℚ)) ^ j)) - ((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j)
      else 2 / ((5 - p : ℚ)) ^ j + 2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ) with hBdef
  set C : ℕ → ℝ := fun l => (((if l = 0 then
      (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
      else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ) with hCdef
  have hrow : (∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then gU else if j' ≤ 8 then
              -((1 : ℚ) / ((j' : ℚ) * ((5 - p : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((p + 1 : ℚ)) ^ j')
              else 2 / ((5 - p : ℚ)) ^ j' + 2 / ((p + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
          A i * B j' * C l * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAdef, hBdef, hCdef]
  rw [hrow, ← int_prod3 (p : ℝ) (q : ℝ) hPQ.le A B C 10 10 9]
  refine intervalIntegral.integral_mono_on hPQ.le ?_ ?_ ?_
  · exact (logQD_continuousOn hPQ.le hp2 hQ4).intervalIntegrable
  · refine (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j' ∈ range 10, B j' * (x - (p : ℝ)) ^ j') *
        (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)).intervalIntegrable _ _
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (p : ℝ) with htdef
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htH : t ≤ (q : ℝ) - (p : ℝ) := by rw [htdef]; linarith
    have hPm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hPp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    have h5p : (0 : ℝ) < 5 - (p : ℝ) := by linarith
    set u : ℝ := t / ((p : ℝ) - 1) with hudef
    set v : ℝ := t / ((p : ℝ) + 1) with hvdef
    set sm : ℝ := t / (5 - (p : ℝ)) with hsdef
    set w : ℝ := t / (p : ℝ) with hwdef
    have hu0 : 0 ≤ u := div_nonneg ht0 hPm1.le
    have hu1 : u ≤ 1 / 2 := by
      rw [hudef, div_le_iff₀ hPm1]; nlinarith [hs1, htH]
    have hv0 : 0 ≤ v := div_nonneg ht0 hPp1.le
    have hv1 : v ≤ 1 / 2 := by
      rw [hvdef, div_le_iff₀ hPp1]; nlinarith [hs2, htH]
    have hs0 : 0 ≤ sm := div_nonneg ht0 h5p.le
    have hs1' : sm ≤ 1 / 2 := by
      rw [hsdef, div_le_iff₀ h5p]; nlinarith [htH]
    have hw0 : 0 ≤ w := div_nonneg ht0 hP0.le
    have hw1 : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ hP0]; nlinarith [hs2, htH]
    -- coefficient identities
    have hArow : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i)
        = (lU : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) + 2 * u ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : A 0 = (lU : ℝ) := by simp only [hAdef, ↓reduceIte]
      have e9 : A 9 = 2 / ((p : ℝ) - 1) ^ 9 := by
        simp only [hAdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, A (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hAi : A (i + 1) = (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) - 1) ^ (i + 1) := by
          simp only [hAdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hAi]
        rw [show u ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) - 1) ^ (i + 1) from by
          rw [hudef, div_pow]]
        ring
      rw [hmid]
      rw [show 2 / ((p : ℝ) - 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * u ^ 9 from by
        rw [show u ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) - 1) ^ 9 from by rw [hudef, div_pow]]
        field_simp]
      ring
    have hBrow : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
        = (gU : ℝ) - (∑ i ∈ range 8, sm ^ (i + 1) / (i + 1))
          - (∑ i ∈ range 8, (-1 : ℝ) ^ i * v ^ (i + 1) / (i + 1)) + 2 * sm ^ 9 + 2 * v ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : B 0 = (gU : ℝ) := by simp only [hBdef, ↓reduceIte]
      have e9 : B 9 = 2 / (5 - (p : ℝ)) ^ 9 + 2 / ((p : ℝ) + 1) ^ 9 := by
        simp only [hBdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, B (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-(sm ^ (i + 1) / (i + 1)) - (-1 : ℝ) ^ i * v ^ (i + 1) / (i + 1)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hBi : B (i + 1) = -(1 / ((i : ℝ) + 1)) / (5 - (p : ℝ)) ^ (i + 1)
            - (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) + 1) ^ (i + 1) := by
          simp only [hBdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hBi]
        rw [show sm ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / (5 - (p : ℝ)) ^ (i + 1) from by
          rw [hsdef, div_pow]]
        rw [show v ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) + 1) ^ (i + 1) from by
          rw [hvdef, div_pow]]
        ring
      rw [hmid, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      have h2a : 2 / (5 - (p : ℝ)) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * sm ^ 9 := by
        rw [hsdef, div_pow]
        ring
      have h2b : 2 / ((p : ℝ) + 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * v ^ 9 := by
        rw [hvdef, div_pow]
        ring
      have h2ab : (2 / (5 - (p : ℝ)) ^ 9 + 2 / ((p : ℝ) + 1) ^ 9) * (x - (p : ℝ)) ^ (8 + 1)
          = 2 * sm ^ 9 + 2 * v ^ 9 := by
        rw [show (8:ℕ) + 1 = 9 by norm_num, add_mul, h2a, h2b]
      rw [h2ab]
      ring
    have hCrow : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
        = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
          + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
      rw [Finset.sum_range_succ']
      have eC0 : C 0 = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
        simp only [hCdef, ↓reduceIte]
        push_cast
        ring
      rw [eC0]
      have hmid : (∑ l ∈ range 8, C (l + 1) * (x - (p : ℝ)) ^ (l + 1))
          = (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hCl : C (l + 1) = (-1 : ℝ) ^ (l + 1) / (p : ℝ) ^ (l + 2) := by
          simp only [hCdef]
          rw [if_neg (by omega : l + 1 ≠ 0)]
          push_cast
          field_simp
        rw [hCl]
        rw [show (-w) ^ (l + 1) = (-1 : ℝ) ^ (l + 1) * (x - (p : ℝ)) ^ (l + 1) / (p : ℝ) ^ (l + 1) from by
          rw [hwdef, show -(t / (p:ℝ)) = -((x - (p:ℝ)) / (p:ℝ)) from by rw [htdef], neg_pow, div_pow]
          ring]
        field_simp
        rw [pow_succ]
        ring
      rw [hmid]
      ring
    -- the three lower bounds on the true factors
    have hAle : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) ≥ Real.log (x - 1) := by
      rw [hArow]
      have hx1 : x - 1 = ((p : ℝ) - 1) * (1 + u) := by
        rw [show 1 + u = (x - 1) / ((p : ℝ) - 1) from by
          rw [hudef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_mul (by linarith) (by linarith)]
      have h := log_one_add_le9 hu0 hu1
      linarith
    have hBle : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) ≥ Real.log (5 * (5 - x) / (x + 1)) := by
      rw [hBrow]
      have h1m : 1 - sm = (5 - x) / (5 - (p : ℝ)) := by
        rw [hsdef]
        field_simp
        ring
      have h1p : 1 + v = (x + 1) / ((p : ℝ) + 1) := by
        rw [hvdef]
        field_simp
        ring
      have hsplit : 5 * (5 - x) / (x + 1)
          = (5 * (5 - (p : ℝ)) / ((p : ℝ) + 1)) * ((1 - sm) / (1 + v)) := by
        rw [h1m, h1p]
        field_simp
      have hpos5 : (0 : ℝ) < 5 * (5 - (p : ℝ)) / ((p : ℝ) + 1) := by
        apply div_pos (by nlinarith) (by linarith)
      have h1s : (0 : ℝ) < 1 - sm := by linarith
      have h1v : (0 : ℝ) < 1 + v := by linarith
      have hdiv : (0 : ℝ) < (1 - sm) / (1 + v) := div_pos h1s h1v
      rw [hsplit, Real.log_mul hpos5.ne' hdiv.ne', Real.log_div h1s.ne' h1v.ne']
      have h1 := log_one_sub_le (s := sm) hs0 hs1' 8
      rw [show (8 : ℕ) + 1 = 9 from rfl] at h1
      have h2 := log_one_add_le9 hv0 hv1
      have h3 := log_one_add_ge9 hv0 hv1
      linarith [hlG, h1, h2, h3]
    have hCle : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≥ 1 / x := by
      rw [hCrow]
      have hsum : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := (inv_geom_bounds (p := (p : ℝ)) (h := (q : ℝ) - (p : ℝ)) hP0 (by linarith) hs2 8
        (t := t) ⟨ht0, htH⟩).2
      rw [show -(t / (p : ℝ)) = -w from by rw [hwdef]] at hg
      rw [show (p : ℝ) + t = x from by rw [htdef]; ring, hsum] at hg
      calc (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 + ∑ l ∈ range 8, (-w) ^ (l + 1)) * (1 / (p : ℝ))
            + (1 / (p : ℝ)) * ((((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
            rw [show (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) = (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 from by norm_num]
            ring
        _ ≥ 1 / x := hg
    -- nonnegativity
    have hf0 : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
    have hg0 : 0 ≤ Real.log (5 * (5 - x) / (x + 1)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hA0 : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) := hf0.trans hAle
    have hB0 : 0 ≤ (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) := hg0.trans hBle
    have hC0 : 0 ≤ (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by
      have hx0 : (0:ℝ) < x := by linarith
      have : (0:ℝ) < 1 / x := by exact div_pos one_pos hx0
      linarith [hCle]
    have hxpos : (0 : ℝ) < x := by linarith
    -- the product comparison
    have h1 : Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1))
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 * (5 - x) / (x + 1)) :=
      mul_le_mul_of_nonneg_right hAle hg0
    have h2 : Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1))
          * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 * (5 - x) / (x + 1))
          * (1 / x) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 * (5 - x) / (x + 1))
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) :=
      mul_le_mul_of_nonneg_left hBle hA0
    have h4 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 * (5 - x) / (x + 1))
          * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (1 / x) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
      mul_le_mul_of_nonneg_left hCle (mul_nonneg hA0 hB0)
    have h6 : Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x
        = Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) * (1 / x) := by
      simp only [div_eq_mul_inv]
      ring
    rw [h6]
    linarith [h2, h4, h5]


private lemma logQD_upper_bounds (j : ℕ) :
    Real.log ((2 + 2 * (j : ℚ) / 16 : ℚ) - 1 : ℝ) ≤
      ((2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2) : ℚ) : ℝ) := by
  have hc := rat_logUpper_cast 20 (2 + 2 * (j : ℚ) / 16 - 1)
  have hb := (Wu04Integral.log_bounds 20 (y := ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ))
    (by
      have h : (1 : ℚ) ≤ 2 + 2 * (j : ℚ) / 16 - 1 := by
        have h0 : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
        linarith
      exact_mod_cast h)).2
  have hcast : ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ) = ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) - 1 := by
    push_cast
    ring
  rw [hcast] at hc hb
  linarith [hc, hb]

private lemma Q_partition_upper :
    (∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      ≤ ∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  set a : ℕ → ℝ := fun j => ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) with hadef
  have ha0 : a 0 = 2 := by rw [hadef]; norm_num
  have ha16 : a 16 = 4 := by rw [hadef]; norm_num
  have hint : ∀ k < 16, IntervalIntegrable
      (fun x : ℝ => Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ a k := by
      rw [hadef]; push_cast
      have h : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hle : a k ≤ a (k + 1) := by
      rw [hadef]; push_cast
      have h : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
      linarith
    have hk4 : a (k + 1) ≤ 4 := by
      rw [hadef]; push_cast
      have hk16 : (k : ℝ) + 1 ≤ 16 := by
        have : k + 1 ≤ 16 := by omega
        exact_mod_cast this
      linarith
    exact (logQD_continuousOn hle hk2 hk4).intervalIntegrable
  have hcell : ∀ j ∈ range 16,
      (∫ x in a j..a (j + 1), Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
        ≤ ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    intro j hj
    have hj16 : j < 16 := Finset.mem_range.mp hj
    have hp2 : (2 : ℚ) ≤ 2 + 2 * (j : ℚ) / 16 := by
      have h : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
      linarith
    have hq4 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 ≤ 4 := by
      have hj1 : ((j + 1 : ℕ) : ℚ) ≤ 16 := by
        have h : j + 1 ≤ 16 := by omega
        exact_mod_cast h
      nlinarith
    have hpq : 2 + 2 * (j : ℚ) / 16 < 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 := by
      have h : (j : ℚ) < ((j + 1 : ℕ) : ℚ) := by
        have h' : j < j + 1 := by omega
        exact_mod_cast h'
      linarith
    have hsmall : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) ≤
        (2 + 2 * (j : ℚ) / 16 - 1) / 2 := by
      have h1 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) = 2 / 16 := by
        push_cast; ring
      rw [h1]; nlinarith
    have hsmall2 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) ≤
        (2 + 2 * (j : ℚ) / 16) / 2 := by
      have h1 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) = 2 / 16 := by
        push_cast; ring
      rw [h1]; nlinarith
    have hlU : Real.log ((2 + 2 * (j : ℚ) / 16 : ℚ) - 1 : ℝ) ≤ ((2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2) : ℚ) : ℝ) :=
      logQD_upper_bounds j
    have hlG : Real.log (5 * (5 - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) / (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) + 1))
        ≤ ((2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2) : ℚ) : ℝ) := by
      have hc := rat_logUpper_cast 20 (5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1))
      have hy1 : (1 : ℚ) ≤ 5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1) := by
        rw [le_div_iff₀ (by positivity)]
        have h0 : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
        nlinarith
      have hb := (Wu04Integral.log_bounds 20
        (y := ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1) : ℚ) : ℝ))
        (by exact_mod_cast hy1)).2
      have hcast : ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1) : ℚ) : ℝ)
          = 5 * (5 - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) / (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) + 1) := by
        push_cast
        ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hpanel := Q_panel_upper (p := 2 + 2 * (j : ℚ) / 16)
      (q := 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16)
      (lU := 2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2))
      (gU := 2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) hp2 hq4 hpq hsmall hsmall2 hlU hlG
    have hcast2 : ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) = a j := by rw [hadef]
    have hcast3 : ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) = a (j + 1) := by rw [hadef]
    simpa only [hcast2, hcast3] using hpanel
  have hsum_int : (∑ j ∈ range 16, ∫ x in a j..a (j + 1),
      Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      = ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x := by
    have h := sum_integral_adjacent_intervals (a := a) (n := 16)
      (f := fun x : ℝ => Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x) hint
    rw [ha0, ha16] at h
    exact h
  rw [← hsum_int]
  exact Finset.sum_le_sum hcell

private theorem certQ3 :
    8 * ((2 * (∑ k ∈ range 26, ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 53 / (1 - ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 2) : ℚ) + (2 * (∑ k ∈ range 26, (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 53 / (1 - (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 2) : ℚ)) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))
      ≤ 17327241 / 1000000 := by
  decide +kernel

private lemma certQ3R :
    8 * ((2 * (∑ k ∈ range 26, ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 53 / (1 - ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 2) : ℚ) + (2 * (∑ k ∈ range 26, (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 53 / (1 - (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 2) : ℚ)) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))
      ≤ ((17327241 / 1000000 : ℚ) : ℝ) := by
  have h := certQ3
  exact_mod_cast h

private lemma castsumQ : ((∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)) : ℚ) : ℝ) = ∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  push_cast
  ring

private theorem numerical_F3_priv (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : integralTerms F f ω 3 ≤ 17.327241 := by
  have hF3 := F3_elementary (F := F) (f := f) h ω
  rw [hF3]
  have hrec : (∫ t in (327/125:ℝ)..3, 1 / (t * (1 - t / 6))) = Real.log (141 / 109) := by
    rw [reciprocal_head (a := (327/125 : ℝ)) (by norm_num) (by norm_num)]
    norm_num
  have hform3 : (∫ t in (3:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) /
        (t * (1 - t / 6)))
      = ∫ t in (3:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
          (1 / (t * (1 - t / 6))) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [div_eq_mul_inv, one_div]
  rw [hrec, hform3, F3_inner_identity]
  -- logarithm bounds
  have h1 : Real.log (141 / 109) ≤ ((2 * (∑ k ∈ range 26, ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 53 / (1 - ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 2) : ℚ) : ℝ) := by
    have hc := rat_logUpper_cast 26 (141 / 109 : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((141 / 109 : ℚ) : ℝ)) (by norm_num)).2
    have hcast : ((141 / 109 : ℚ) : ℝ) = 141 / 109 := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have h2 : Real.log 5 ≤ ((2 * (∑ k ∈ range 26, (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 53 / (1 - (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 2) : ℚ) : ℝ) := by
    have hc := rat_logUpper_cast 26 (5 : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((5 : ℚ) : ℝ)) (by norm_num)).2
    have hcast : ((5 : ℚ) : ℝ) = (5 : ℝ) := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have hP := Q_partition_upper
  have hc3 := certQ3R
  rw [castsumQ] at hc3
  have hmain : 8 * Real.log (141 / 109) + 8 * (Real.log 5 +
      ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x) ≤
      ((17327241 / 1000000 : ℚ) : ℝ) := by
    nlinarith [h1, h2, hP, hc3]
  calc 8 * Real.log (141 / 109) + 8 * (Real.log 5 +
        ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      ≤ ((17327241 / 1000000 : ℚ) : ℝ) := hmain
    _ = 17.327241 := by norm_num

private theorem certQ2 : 8 * ((2 * (∑ k ∈ range 26, (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 53 / (1 - (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 2)) - (2 * (∑ k ∈ range 26, (((141 / 109 : ℚ) - 1) / ((141 / 109 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)))) ≤ 3104857 / 1000000 := by
  decide +kernel

private lemma log_step_F2 : 8 * (Real.log (82 / 43) - Real.log (141 / 109)) ≤ 3104857 / 1000000 := by
  have ha : Real.log (82 / 43) ≤ ((2 * (∑ k ∈ range 26, (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 53 / (1 - (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 2)) : ℝ) := by
    have hc := rat_logUpper_cast 26 (82 / 43 : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((82 / 43 : ℚ) : ℝ)) (by norm_num)).2
    have hcast : ((82 / 43 : ℚ) : ℝ) = 82 / 43 := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have hb2 : ((2 * (∑ k ∈ range 26, (((141 / 109 : ℚ) - 1) / ((141 / 109 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1))) : ℝ) ≤ Real.log (141 / 109) := by
    have hc := rat_logLower_cast' 26 (141 / 109 : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((141 / 109 : ℚ) : ℝ)) (by norm_num)).1
    have hcast : ((141 / 109 : ℚ) : ℝ) = 141 / 109 := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have hcert : 8 * ((2 * (∑ k ∈ range 26, (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 53 / (1 - (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 2)) - (2 * (∑ k ∈ range 26, (((141 / 109 : ℚ) - 1) / ((141 / 109 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)))) ≤ (3104857 / 1000000 : ℚ) := certQ2
  have hcertR : 8 * ((2 * (∑ k ∈ range 26, (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 53 / (1 - (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 2)) - (2 * (∑ k ∈ range 26, (((141 / 109 : ℚ) - 1) / ((141 / 109 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)))) ≤ ((3104857 / 1000000 : ℚ) : ℝ) := by
    have h := hcert
    exact_mod_cast h
  linarith [ha, hb2, hcertR]

/-! ### The panel upper bound for `∫ log (x-1) log (5/(x+1)) / x` -/

private lemma P_panel_upper (p q : ℚ) (hp : 2 ≤ p) (hq : q ≤ 4) (hpq : p < q)
    (hsmall : q - p ≤ (p - 1) / 2) (hsmall2 : q - p ≤ p / 2)
    (lU gU : ℚ)
    (hlU : Real.log ((p : ℝ) - 1) ≤ (lU : ℝ))
    (hlG : Real.log (5 / ((p : ℝ) + 1)) ≤ (gU : ℝ)) :
    (∫ x in (p : ℝ)..(q : ℝ), Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
      ≤ ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then gU else if j' ≤ 8 then
              -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((p + 1 : ℚ)) ^ j')
              else 2 / ((p + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hP1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hPQ : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hQ4 : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hs1 : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ (((p - 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall
    push_cast at this ⊢
    linarith
  have hs2 : (q : ℝ) - (p : ℝ) ≤ (p : ℝ) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ ((p / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall2
    push_cast at this ⊢
    linarith
  set A : ℕ → ℝ := fun i => (((if i = 0 then lU else if i ≤ 8 then
      (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i) else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
    with hAdef
  set B : ℕ → ℝ := fun j => (((if j = 0 then gU else if j ≤ 8 then
      -((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j)
      else 2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ) with hBdef
  set C : ℕ → ℝ := fun l => (((if l = 0 then
      (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
      else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ) with hCdef
  have hrow : (∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then gU else if j' ≤ 8 then
              -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((p + 1 : ℚ)) ^ j')
              else 2 / ((p + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
          A i * B j' * C l * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAdef, hBdef, hCdef]
  rw [hrow, ← int_prod3 (p : ℝ) (q : ℝ) hPQ.le A B C 10 10 9]
  refine intervalIntegral.integral_mono_on hPQ.le ?_ ?_ ?_
  · exact (logP_continuousOn hPQ.le hp2).intervalIntegrable
  · refine (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j' ∈ range 10, B j' * (x - (p : ℝ)) ^ j') *
        (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)).intervalIntegrable _ _
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (p : ℝ) with htdef
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htH : t ≤ (q : ℝ) - (p : ℝ) := by rw [htdef]; linarith
    have hPm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hPp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    set u : ℝ := t / ((p : ℝ) - 1) with hudef
    set v : ℝ := t / ((p : ℝ) + 1) with hvdef
    set w : ℝ := t / (p : ℝ) with hwdef
    have hu0 : 0 ≤ u := div_nonneg ht0 hPm1.le
    have hu1 : u ≤ 1 / 2 := by
      rw [hudef, div_le_iff₀ hPm1]; nlinarith [hs1, htH]
    have hv0 : 0 ≤ v := div_nonneg ht0 hPp1.le
    have hv1 : v ≤ 1 / 2 := by
      rw [hvdef, div_le_iff₀ hPp1]; nlinarith [hs2, htH]
    have hw0 : 0 ≤ w := div_nonneg ht0 hP0.le
    have hw1 : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ hP0]; nlinarith [hs2, htH]
    have hArow : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i)
        = (lU : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) + 2 * u ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : A 0 = (lU : ℝ) := by simp only [hAdef, ↓reduceIte]
      have e9 : A 9 = 2 / ((p : ℝ) - 1) ^ 9 := by
        simp only [hAdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, A (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hAi : A (i + 1) = (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) - 1) ^ (i + 1) := by
          simp only [hAdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hAi]
        rw [show u ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) - 1) ^ (i + 1) from by
          rw [hudef, div_pow]]
        ring
      rw [hmid]
      rw [show 2 / ((p : ℝ) - 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * u ^ 9 from by
        rw [show u ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) - 1) ^ 9 from by rw [hudef, div_pow]]
        field_simp]
      ring
    have hBrow : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
        = (gU : ℝ) - (∑ i ∈ range 8, (-1 : ℝ) ^ i * v ^ (i + 1) / (i + 1)) + 2 * v ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : B 0 = (gU : ℝ) := by simp only [hBdef, ↓reduceIte]
      have e9 : B 9 = 2 / ((p : ℝ) + 1) ^ 9 := by
        simp only [hBdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, B (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, -((-1 : ℝ) ^ i * v ^ (i + 1) / (i + 1)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hBi : B (i + 1) = -((-1 : ℝ) ^ i) / ((i : ℝ) + 1) / ((p : ℝ) + 1) ^ (i + 1) := by
          simp only [hBdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hBi]
        rw [show v ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) + 1) ^ (i + 1) from by
          rw [hvdef, div_pow]]
        ring
      rw [hmid, Finset.sum_neg_distrib]
      have h2a : 2 / ((p : ℝ) + 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * v ^ 9 := by
        rw [hvdef, div_pow]
        ring
      rw [h2a]
      ring
    have hCrow : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
        = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
          + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
      rw [Finset.sum_range_succ']
      have eC0 : C 0 = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
        simp only [hCdef, ↓reduceIte]
        push_cast
        ring
      rw [eC0]
      have hmid : (∑ l ∈ range 8, C (l + 1) * (x - (p : ℝ)) ^ (l + 1))
          = (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hCl : C (l + 1) = (-1 : ℝ) ^ (l + 1) / (p : ℝ) ^ (l + 2) := by
          simp only [hCdef]
          rw [if_neg (by omega : l + 1 ≠ 0)]
          push_cast
          field_simp
        rw [hCl]
        rw [show (-w) ^ (l + 1) = (-1 : ℝ) ^ (l + 1) * (x - (p : ℝ)) ^ (l + 1) / (p : ℝ) ^ (l + 1) from by
          rw [hwdef, show -(t / (p:ℝ)) = -((x - (p:ℝ)) / (p:ℝ)) from by rw [htdef], neg_pow, div_pow]
          ring]
        field_simp
        rw [pow_succ]
        ring
      rw [hmid]
      ring
    have hAle : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) ≥ Real.log (x - 1) := by
      rw [hArow]
      have hx1 : x - 1 = ((p : ℝ) - 1) * (1 + u) := by
        rw [show 1 + u = (x - 1) / ((p : ℝ) - 1) from by
          rw [hudef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_mul (by linarith) (by linarith)]
      have h := log_one_add_le9 hu0 hu1
      linarith
    have hBle : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) ≥ Real.log (5 / (x + 1)) := by
      rw [hBrow]
      have h1p : 1 + v = (x + 1) / ((p : ℝ) + 1) := by
        rw [hvdef]; field_simp; ring
      have hsplit : 5 / (x + 1) = (5 / ((p : ℝ) + 1)) * (1 / (1 + v)) := by
        rw [h1p]; field_simp
      have hpos5 : (0 : ℝ) < 5 / ((p : ℝ) + 1) := by positivity
      have h1v : (0 : ℝ) < 1 + v := by linarith
      rw [hsplit, Real.log_mul hpos5.ne' (by positivity), Real.log_div one_pos.ne' h1v.ne',
        Real.log_one]
      have h2 := log_one_add_le9 hv0 hv1
      have h3 := log_one_add_ge9 hv0 hv1
      linarith [hlG, h2, h3]
    have hCle : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≥ 1 / x := by
      rw [hCrow]
      have hsum : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := (inv_geom_bounds (p := (p : ℝ)) (h := (q : ℝ) - (p : ℝ)) hP0 (by linarith) hs2 8
        (t := t) ⟨ht0, htH⟩).2
      rw [show -(t / (p : ℝ)) = -w from by rw [hwdef]] at hg
      rw [show (p : ℝ) + t = x from by rw [htdef]; ring, hsum] at hg
      calc (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 + ∑ l ∈ range 8, (-w) ^ (l + 1)) * (1 / (p : ℝ))
            + (1 / (p : ℝ)) * ((((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by ring
        _ ≥ 1 / x := hg
    have hf0 : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
    have hg0 : 0 ≤ Real.log (5 / (x + 1)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hA0 : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) := hf0.trans hAle
    have hB0 : 0 ≤ (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) := hg0.trans hBle
    have hC0 : 0 ≤ (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by
      have hx0 : (0:ℝ) < x := by linarith
      have : (0:ℝ) < 1 / x := by exact div_pos one_pos hx0
      linarith [hCle]
    have h1 : Real.log (x - 1) * Real.log (5 / (x + 1))
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 / (x + 1)) :=
      mul_le_mul_of_nonneg_right hAle hg0
    have hx0 : (0:ℝ) < x := by linarith
    have h2 : Real.log (x - 1) * Real.log (5 / (x + 1)) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 / (x + 1)) * (1 / x) :=
      mul_le_mul_of_nonneg_right h1 (by exact le_of_lt (div_pos one_pos hx0))
    have h3 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 / (x + 1))
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) :=
      mul_le_mul_of_nonneg_left hBle hA0
    have h4 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 / (x + 1)) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (1 / x) :=
      mul_le_mul_of_nonneg_right h3 (by exact le_of_lt (div_pos one_pos hx0))
    have h5 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
      mul_le_mul_of_nonneg_left hCle (mul_nonneg hA0 hB0)
    have h6 : Real.log (x - 1) * Real.log (5 / (x + 1)) / x
        = Real.log (x - 1) * Real.log (5 / (x + 1)) * (1 / x) := by
      simp only [div_eq_mul_inv]
      ring
    rw [h6]
    linarith [h2, h4, h5]

/-! ### The panel upper bound for `∫ log (x-1) / x` (the `J` terms of `F1`) -/

private lemma J_panel_upper (p q : ℚ) (hp : 2 ≤ p) (hq : q ≤ 4) (hpq : p < q)
    (hsmall : q - p ≤ (p - 1) / 2) (hsmall2 : q - p ≤ p / 2)
    (lU : ℚ) (hlU : Real.log ((p : ℝ) - 1) ≤ (lU : ℝ)) :
    (∫ x in (p : ℝ)..(q : ℝ), Real.log (x - 1) / x)
      ≤ ∑ l ∈ range 9, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hPQ : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hq4 : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hs1 : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ (((p - 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall
    push_cast at this ⊢
    linarith
  have hs2 : (q : ℝ) - (p : ℝ) ≤ (p : ℝ) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ ((p / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall2
    push_cast at this ⊢
    linarith
  set A : ℕ → ℝ := fun i => (((if i = 0 then lU else if i ≤ 8 then
      (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i) else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
    with hAdef
  set B : ℕ → ℝ := fun _ => 1 with hBdef
  set C : ℕ → ℝ := fun l => (((if l = 0 then
      (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
      else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ) with hCdef
  have hrow : (∑ l ∈ range 9, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range 9, ∑ j' ∈ range 1, ∑ i ∈ range 10,
          A i * B j' * C l * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) /
            ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAdef, hBdef, hCdef, Finset.sum_range_one]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => ?_))
    norm_num
  rw [hrow, ← int_prod3 (p : ℝ) (q : ℝ) hPQ.le A B C 10 1 9]
  refine intervalIntegral.integral_mono_on hPQ.le ?_ ?_ ?_
  · exact (logquot_continuousOn.mono (by
      intro x hx
      rw [Set.uIcc_of_le hPQ.le] at hx
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
      exact ⟨by linarith [hx.1], by linarith [hx.2, hq4]⟩)).intervalIntegrable
  · refine (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j' ∈ range 1, B j' * (x - (p : ℝ)) ^ j') *
        (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)).intervalIntegrable _ _
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (p : ℝ) with htdef
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htH : t ≤ (q : ℝ) - (p : ℝ) := by rw [htdef]; linarith
    have hPm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hPp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    set u : ℝ := t / ((p : ℝ) - 1) with hudef
    set w : ℝ := t / (p : ℝ) with hwdef
    have hu0 : 0 ≤ u := div_nonneg ht0 hPm1.le
    have hu1 : u ≤ 1 / 2 := by
      rw [hudef, div_le_iff₀ hPm1]; nlinarith [hs1, htH]
    have hw0 : 0 ≤ w := div_nonneg ht0 hP0.le
    have hw1 : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ hP0]; nlinarith [hs2, htH]
    have hBone : (∑ j' ∈ range 1, B j' * (x - (p : ℝ)) ^ j') = 1 := by
      simp only [Finset.sum_range_one, hBdef]
      norm_num
    have hArow : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i)
        = (lU : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) + 2 * u ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : A 0 = (lU : ℝ) := by simp only [hAdef, ↓reduceIte]
      have e9 : A 9 = 2 / ((p : ℝ) - 1) ^ 9 := by
        simp only [hAdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, A (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hAi : A (i + 1) = (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) - 1) ^ (i + 1) := by
          simp only [hAdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hAi]
        rw [show u ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) - 1) ^ (i + 1) from by
          rw [hudef, div_pow]]
        ring
      rw [hmid]
      rw [show 2 / ((p : ℝ) - 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * u ^ 9 from by
        rw [show u ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) - 1) ^ 9 from by rw [hudef, div_pow]]
        field_simp]
      ring
    have hCrow : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
        = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
          + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
      rw [Finset.sum_range_succ']
      have eC0 : C 0 = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
        simp only [hCdef, ↓reduceIte]
        push_cast
        ring
      rw [eC0]
      have hmid : (∑ l ∈ range 8, C (l + 1) * (x - (p : ℝ)) ^ (l + 1))
          = (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hCl : C (l + 1) = (-1 : ℝ) ^ (l + 1) / (p : ℝ) ^ (l + 2) := by
          simp only [hCdef]
          rw [if_neg (by omega : l + 1 ≠ 0)]
          push_cast
          field_simp
        rw [hCl]
        rw [show (-w) ^ (l + 1) = (-1 : ℝ) ^ (l + 1) * (x - (p : ℝ)) ^ (l + 1) / (p : ℝ) ^ (l + 1) from by
          rw [hwdef, show -(t / (p:ℝ)) = -((x - (p:ℝ)) / (p:ℝ)) from by rw [htdef], neg_pow, div_pow]
          ring]
        field_simp
        rw [pow_succ]
        ring
      rw [hmid]
      ring
    have hAle : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) ≥ Real.log (x - 1) := by
      rw [hArow]
      have hx1 : x - 1 = ((p : ℝ) - 1) * (1 + u) := by
        rw [show 1 + u = (x - 1) / ((p : ℝ) - 1) from by
          rw [hudef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_mul (by linarith) (by linarith)]
      have h := log_one_add_le9 hu0 hu1
      linarith
    have hCle : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≥ 1 / x := by
      rw [hCrow]
      have hsum : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := (inv_geom_bounds (p := (p : ℝ)) (h := (q : ℝ) - (p : ℝ)) hP0 (by linarith) hs2 8
        (t := t) ⟨ht0, htH⟩).2
      rw [show -(t / (p : ℝ)) = -w from by rw [hwdef]] at hg
      rw [show (p : ℝ) + t = x from by rw [htdef]; ring, hsum] at hg
      calc (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 + ∑ l ∈ range 8, (-w) ^ (l + 1)) * (1 / (p : ℝ))
            + (1 / (p : ℝ)) * ((((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by ring
        _ ≥ 1 / x := hg
    have hf0 : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
    have hA0 : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) := hf0.trans hAle
    have hx0 : (0:ℝ) < x := by linarith
    have hC0 : 0 ≤ (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by
      have : (0:ℝ) < 1 / x := by exact div_pos one_pos hx0
      linarith [hCle]
    have h1 : Real.log (x - 1) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (1 / x) :=
      mul_le_mul_of_nonneg_right hAle (by exact le_of_lt (div_pos one_pos hx0))
    have h2 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
      mul_le_mul_of_nonneg_left hCle hA0
    have h3 : Real.log (x - 1) / x = Real.log (x - 1) * (1 / x) := by
      simp only [div_eq_mul_inv]
      ring
    have h4 : (∑ j' ∈ range 1, B j' * (x - (p : ℝ)) ^ j') = 1 := hBone
    rw [h3]
    calc Real.log (x - 1) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (1 / x) := h1
      _ ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := h2
      _ = (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
            (∑ j' ∈ range 1, B j' * (x - (p : ℝ)) ^ j') *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by rw [hBone]; ring

/-! ### The `F1` panel partitions and leaf -/

private lemma P_partition_F1 :
    (∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x) ≤ ∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16) : ℚ) : ℝ) - (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  set a : ℕ → ℝ := fun j => ((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) with hadef
  have ha0 : a 0 = 67/29 := by rw [hadef]; norm_num
  have ha16 : a 16 = 4 := by rw [hadef]; norm_num
  have hint : ∀ k < 16, IntervalIntegrable
      (fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ a k := by
      rw [hadef]; push_cast
      have h : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hle : a k ≤ a (k + 1) := by
      rw [hadef]; push_cast
      have h : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
      linarith
    exact (logP_continuousOn hle hk2).intervalIntegrable
  have hcell : ∀ j ∈ range 16,
      (∫ x in a j..a (j + 1), Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
        ≤ ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16) : ℚ) : ℝ) - (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    intro j hj
    have hj16 : j < 16 := Finset.mem_range.mp hj
    have hp2 : (2 : ℚ) ≤ 67 / 29 + (49 / 29) * (j : ℚ) / 16 := by
      have h : 0 ≤ (49 / 29) * (j : ℚ) / 16 := by positivity
      linarith
    have hq4 : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 ≤ 4 := by
      have hj1 : ((j + 1 : ℕ) : ℚ) ≤ 16 := by
        have h : j + 1 ≤ 16 := by omega
        exact_mod_cast h
      nlinarith
    have hpq : 67 / 29 + (49 / 29) * (j : ℚ) / 16 < 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 := by
      have h : (j : ℚ) < ((j + 1 : ℕ) : ℚ) := by
        have h' : j < j + 1 := by omega
        exact_mod_cast h'
      linarith
    have hsmall : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 - (67 / 29 + (49 / 29) * (j : ℚ) / 16)
        ≤ (67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) / 2 := by
      have h1 : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 - (67 / 29 + (49 / 29) * (j : ℚ) / 16)
          = 49 / 464 := by push_cast; ring
      rw [h1]; nlinarith
    have hsmall2 : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 - (67 / 29 + (49 / 29) * (j : ℚ) / 16)
        ≤ (67 / 29 + (49 / 29) * (j : ℚ) / 16) / 2 := by
      have h1 : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 - (67 / 29 + (49 / 29) * (j : ℚ) / 16)
          = 49 / 464 := by push_cast; ring
      rw [h1]; nlinarith
    have hlU : Real.log ((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) - 1 : ℝ)
        ≤ (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2) : ℚ) := by
      have hc := rat_logUpper_cast 20 (67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1)
      have hy1 : (1 : ℚ) ≤ 67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1 := by
        have h : 0 ≤ (49 / 29) * (j : ℚ) / 16 := by positivity
        linarith
      have hb := (Wu04Integral.log_bounds 20
        (y := ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1 : ℚ) : ℝ)) (by exact_mod_cast hy1)).2
      have hcast : ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1 : ℚ) : ℝ)
          = ((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) - 1 := by push_cast; ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hlG : Real.log (5 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) + 1))
        ≤ (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2) : ℚ) := by
      have hc := rat_logUpper_cast 20 (5 / (67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))
      have hy1 : (1 : ℚ) ≤ 5 / (67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) := by
        rw [le_div_iff₀ (by positivity)]
        have h : 0 ≤ (49 / 29) * (j : ℚ) / 16 := by positivity
        linarith
      have hb := (Wu04Integral.log_bounds 20
        (y := ((5 / (67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ) : ℝ)) (by exact_mod_cast hy1)).2
      have hcast : ((5 / (67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ) : ℝ)
          = 5 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) + 1) := by push_cast; ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hpanel := P_panel_upper (p := 67 / 29 + (49 / 29) * (j : ℚ) / 16)
      (q := 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)
      (lU := 2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) (gU := 2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2))
      hp2 hq4 hpq hsmall hsmall2 hlU hlG
    have hcast2 : ((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) = a j := by rw [hadef]
    have hcast3 : ((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) = a (j + 1) := by rw [hadef]
    simpa only [hcast2, hcast3] using hpanel
  have hsum_int : (∑ j ∈ range 16, ∫ x in a j..a (j + 1),
      Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
      = ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
    have h := sum_integral_adjacent_intervals (a := a) (n := 16)
      (f := fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) hint
    rw [ha0, ha16] at h
    exact h
  rw [← hsum_int]
  exact Finset.sum_le_sum hcell

private lemma J_partition_F1 :
    (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) ≤ ∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := by
  set a : ℕ → ℝ := fun j => ((2 + (9 / 29) * (j : ℚ) / 8 : ℚ) : ℝ) with hadef
  have ha0 : a 0 = 2 := by rw [hadef]; norm_num
  have ha8 : a 8 = 67/29 := by rw [hadef]; norm_num
  have hint : ∀ k < 8, IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ a k := by
      rw [hadef]; push_cast
      have h : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hle : a k ≤ a (k + 1) := by
      rw [hadef]; push_cast
      have h : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
      linarith
    have hk4 : a (k + 1) ≤ 4 := by
      rw [hadef]; push_cast
      have hk8 : (k : ℝ) + 1 ≤ 8 := by
        have : k + 1 ≤ 8 := by omega
        exact_mod_cast this
      linarith
    exact (logquot_continuousOn.mono (by
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
      exact ⟨by linarith [hx.1], by linarith [hx.2, hk4]⟩)).intervalIntegrable
  have hcell : ∀ j ∈ range 8,
      (∫ x in a j..a (j + 1), Real.log (x - 1) / x)
        ≤ ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := by
    intro j hj
    have hj8 : j < 8 := Finset.mem_range.mp hj
    have hp2 : (2 : ℚ) ≤ 2 + (9 / 29) * (j : ℚ) / 8 := by
      have h : 0 ≤ (9 / 29) * (j : ℚ) / 8 := by positivity
      linarith
    have hq4 : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 ≤ 4 := by
      have hj1 : ((j + 1 : ℕ) : ℚ) ≤ 8 := by
        have h : j + 1 ≤ 8 := by omega
        exact_mod_cast h
      nlinarith
    have hpq : 2 + (9 / 29) * (j : ℚ) / 8 < 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 := by
      have h : (j : ℚ) < ((j + 1 : ℕ) : ℚ) := by
        have h' : j < j + 1 := by omega
        exact_mod_cast h'
      linarith
    have hsmall : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 - (2 + (9 / 29) * (j : ℚ) / 8)
        ≤ (2 + (9 / 29) * (j : ℚ) / 8 - 1) / 2 := by
      have h1 : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 - (2 + (9 / 29) * (j : ℚ) / 8) = 9 / 232 := by
        push_cast; ring
      rw [h1]; nlinarith
    have hsmall2 : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 - (2 + (9 / 29) * (j : ℚ) / 8)
        ≤ (2 + (9 / 29) * (j : ℚ) / 8) / 2 := by
      have h1 : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 - (2 + (9 / 29) * (j : ℚ) / 8) = 9 / 232 := by
        push_cast; ring
      rw [h1]; nlinarith
    have hlU : Real.log ((2 + (9 / 29) * (j : ℚ) / 8 : ℚ) - 1 : ℝ) ≤ (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2) : ℚ) := by
      have hc := rat_logUpper_cast 20 (2 + (9 / 29) * (j : ℚ) / 8 - 1)
      have hy1 : (1 : ℚ) ≤ 2 + (9 / 29) * (j : ℚ) / 8 - 1 := by
        have h : 0 ≤ (9 / 29) * (j : ℚ) / 8 := by positivity
        linarith
      have hb := (Wu04Integral.log_bounds 20
        (y := ((2 + (9 / 29) * (j : ℚ) / 8 - 1 : ℚ) : ℝ)) (by exact_mod_cast hy1)).2
      have hcast : ((2 + (9 / 29) * (j : ℚ) / 8 - 1 : ℚ) : ℝ)
          = ((2 + (9 / 29) * (j : ℚ) / 8 : ℚ) : ℝ) - 1 := by push_cast; ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hpanel := J_panel_upper (p := 2 + (9 / 29) * (j : ℚ) / 8)
      (q := 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) (lU := 2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2))
      hp2 hq4 hpq hsmall hsmall2 hlU
    have hcast2 : ((2 + (9 / 29) * (j : ℚ) / 8 : ℚ) : ℝ) = a j := by rw [hadef]
    have hcast3 : ((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 : ℚ) : ℝ) = a (j + 1) := by rw [hadef]
    simpa only [hcast2, hcast3] using hpanel
  have hsum_int : (∑ j ∈ range 8, ∫ x in a j..a (j + 1), Real.log (x - 1) / x)
      = ∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x := by
    have h := sum_integral_adjacent_intervals (a := a) (n := 8)
      (f := fun x : ℝ => Real.log (x - 1) / x) hint
    rw [ha0, ha8] at h
    exact h
  rw [← hsum_int]
  exact Finset.sum_le_sum hcell

private lemma castsumP : ((∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) * ((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)) : ℚ) : ℝ) = ∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16) : ℚ) : ℝ) - (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  push_cast
  ring

private lemma castsumJ : ((∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) * (if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) * ((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) ^ (i + l + 1) / ((i : ℚ) + (l : ℚ) + 1)) : ℚ) : ℝ) =
      ∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := by
  push_cast
  ring

private lemma F1_inner_identity :
    (∫ t in (96/29:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t))
      = Real.log (5 / (96/29)) + Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        + ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
  have ha : (96/29:ℝ) ≤ 5 := by norm_num
  have hA_cont : ContinuousOn (fun t : ℝ => ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x)
      (Set.uIcc (96/29:ℝ) 5) := by
    have h := continuousOn_primitive_interval' logquot_integrable
      (Set.left_mem_uIcc (a := (2:ℝ)) (b := (4:ℝ)))
    refine h.comp (by fun_prop) ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (96/29:ℝ) ≤ 5)] at ht
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
    constructor <;> linarith [ht.1, ht.2]
  have hinv_cont : ContinuousOn (fun t : ℝ => 1 / t) (Set.uIcc (96/29:ℝ) 5) := by
    rw [Set.uIcc_of_le ha]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; change t ≠ 0; linarith [ht.1]
  have hint2 : IntervalIntegrable
      (fun t : ℝ => (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t)) volume (96/29) 5 :=
    (hA_cont.mul hinv_cont).intervalIntegrable
  have hsplit : (∫ t in (96/29:ℝ)..5,
        (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t))
      = (∫ t in (96/29:ℝ)..5, 1 / t)
        + ∫ t in (96/29:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t) := by
    rw [← intervalIntegral.integral_add hinv_cont.intervalIntegrable hint2]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hlog : (∫ t in (96/29:ℝ)..5, 1 / t) = Real.log (5 / (96/29)) := by
    rw [show (∫ t in (96/29:ℝ)..5, 1 / t) = ∫ t in (96/29:ℝ)..5, (t)⁻¹ from by
      apply intervalIntegral.integral_congr; intro t _; rw [one_div]]
    rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 96/29) (by norm_num : (0:ℝ) < 5)]
  have hAsplit : ∀ t ∈ Set.uIcc (96/29:ℝ) 5,
      (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x)
        = (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
          + ∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x := by
    intro t ht
    rw [Set.uIcc_of_le ha] at ht
    have h1 : (2:ℝ) ≤ 67/29 := by norm_num
    have h2 : (67/29:ℝ) ≤ t - 1 := by linarith [ht.1]
    have hi1 : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume 2 (67/29) :=
      logquot_continuousOn.mono (by
        intro x hx
        rw [Set.uIcc_of_le h1] at hx
        rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
        exact ⟨hx.1, by linarith [hx.2]⟩) |>.intervalIntegrable
    have hi2 : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume (67/29) (t - 1) :=
      logquot_continuousOn.mono (by
        intro x hx
        rw [Set.uIcc_of_le h2] at hx
        rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
        exact ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩) |>.intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hperm : (∫ t in (96/29:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t))
      = (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) * (∫ t in (96/29:ℝ)..5, 1 / t)
        + ∫ t in (96/29:ℝ)..5, (∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t) := by
    have e1 : (∫ t in (96/29:ℝ)..5, (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) * (1 / t))
        = (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) * (∫ t in (96/29:ℝ)..5, 1 / t) := by
      rw [intervalIntegral.integral_const_mul]
    have e2 : IntervalIntegrable
        (fun t : ℝ => (∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t)) volume (96/29) 5 := by
      have hA2 : ContinuousOn (fun t : ℝ => ∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x)
          (Set.uIcc (96/29:ℝ) 5) := by
        have h67 : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume (67/29) 4 := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le (by norm_num : (67/29:ℝ) ≤ 4)]
          apply ContinuousOn.div
          · apply ContinuousOn.log (by fun_prop)
            intro x hx; linarith [hx.1]
          · exact continuousOn_id
          · intro x hx; change x ≠ 0; linarith [hx.1]
        have h := continuousOn_primitive_interval' h67
          (Set.left_mem_uIcc (a := (67/29:ℝ)) (b := (4:ℝ)))
        refine h.comp (by fun_prop) ?_
        intro t ht
        rw [Set.uIcc_of_le ha] at ht
        rw [Set.uIcc_of_le (by norm_num : (67/29:ℝ) ≤ 4)]
        constructor <;> linarith [ht.1, ht.2]
      exact (hA2.mul hinv_cont).intervalIntegrable
    rw [← e1]
    rw [← intervalIntegral.integral_add
      (hinv_cont.intervalIntegrable.const_mul _) e2]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    rw [hAsplit t ht]
    ring
  have hswap := triangle_swap (f := fun x : ℝ => Real.log (x - 1) / x) (h := fun t : ℝ => 1 / t)
    (c := 1) (A := 96/29) (B := 5) (hc := by norm_num) (hAB := by norm_num)
    (hf := by
      rw [show (96/29:ℝ) - 1 = 67/29 by norm_num, show (5:ℝ) - 1 = 4 by norm_num]
      exact logquot_continuousOn.mono (by
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (67/29:ℝ) ≤ 4)] at hx
        rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
        exact ⟨by linarith [hx.1], hx.2⟩))
    (hh := by
      rw [show (96/29:ℝ) = 96/29 by norm_num]
      exact hinv_cont)
  simp only [show (96/29:ℝ) - 1 = 67/29 by norm_num, show (5:ℝ) - 1 = 4 by norm_num] at hswap
  have hweight : ∀ x ∈ Set.uIcc (2:ℝ) 4, (∫ t in (x + 1)..5, 1 / t) = Real.log (5 / (x + 1)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
    rw [show (∫ t in (x + 1)..5, 1 / t) = ∫ t in (x + 1)..5, (t)⁻¹ from by
      apply intervalIntegral.integral_congr; intro t _; rw [one_div]]
    rw [integral_inv_of_pos (by linarith [hx.1] : (0:ℝ) < x + 1) (by norm_num : (0:ℝ) < 5)]
  have hPform : (∫ t in (96/29:ℝ)..5, (∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t))
      = ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
    rw [hswap]
    apply intervalIntegral.integral_congr
    intro x hx
    change Real.log (x - 1) / x * (∫ t in (x + 1)..5, 1 / t)
      = Real.log (x - 1) * Real.log (5 / (x + 1)) / x
    rw [hweight x (by
      rw [Set.uIcc_of_le (by norm_num : (67/29:ℝ) ≤ 4)] at hx
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
      exact ⟨by linarith [hx.1], hx.2⟩)]
    ring
  rw [hsplit, hlog, hperm, hlog, hPform]
  ring

private theorem certF1 :
    8 * ((2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) + (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) * (∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) * (if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) * ((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) ^ (i + l + 1) / ((i : ℚ) + (l : ℚ) + 1))) + (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) * ((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) ≤ 3891854 / 1000000 := by
  decide +kernel

private lemma certF1R :
    8 * ((2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) + (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) * (∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) * (if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) * ((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) ^ (i + l + 1) / ((i : ℚ) + (l : ℚ) + 1))) + (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) * ((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) ≤ ((3891854 / 1000000 : ℚ) : ℝ) := by
  have h := certF1
  exact_mod_cast h

theorem numerical_F1_aux (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : integralTerms F f ω 1 ≤ 3.891854 := by
  have hF1 := F1_elementary (F := F) (f := f) h ω
  rw [hF1]
  rw [show (1 / (2 * kappa2) - 1 : ℝ) = 96/29 by norm_num [kappa2],
    show (1 / (2 * kappa1) - 1 : ℝ) = 5 by norm_num [kappa1]]
  have hform : (∫ t in (96/29:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) / t)
      = ∫ t in (96/29:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [div_eq_mul_inv, one_div]
  rw [hform, F1_inner_identity]
  -- log bounds and the two panel bounds
  have h1 : Real.log (5 / (96/29)) ≤ ((2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) : ℝ) := by
    have hc := rat_logUpper_cast 26 (5 / (96 / 29) : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((5 / (96 / 29) : ℚ) : ℝ)) (by norm_num)).2
    have hcast : ((5 / (96 / 29) : ℚ) : ℝ) = 5 / (96/29) := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have hP := P_partition_F1
  have hJ := J_partition_F1
  have hc := certF1R
  rw [castsumP, castsumJ] at hc
  have h5a : (0:ℝ) ≤ (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) := by
    have := (Wu04Integral.log_bounds 26 (y := ((5 / (96 / 29) : ℚ) : ℝ)) (by norm_num)).1
    have hc2 := rat_logLower_cast' 26 (5 / (96 / 29) : ℚ)
    nlinarith [this, hc2]
  have hlog0 : (0:ℝ) ≤ Real.log (5 / (96/29)) := Real.log_nonneg (by norm_num)
  have hJ0 : (0:ℝ) ≤ ∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    apply div_nonneg _ (by linarith [hx.1])
    apply Real.log_nonneg
    linarith [hx.1]
  have hprod : Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
      ≤ (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) * (∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1))) := by
    have hJsum : (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) ≤ ∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := hJ
    have h2 : Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        ≤ (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) :=
      mul_le_mul_of_nonneg_right h1 hJ0
    have h3 : (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        ≤ (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) * (∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hJsum h5a
    linarith
  have hmain : 8 * (Real.log (5 / (96/29)) +
      (Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        + ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x))
      ≤ ((3891854 / 1000000 : ℚ) : ℝ) := by
    nlinarith [h1, hP, hJ, hc, h5a, hlog0, hJ0, hprod]
  calc 8 * (Real.log (5 / (96/29)) + Real.log (5 / (96/29)) *
        (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        + ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
      = 8 * (Real.log (5 / (96/29)) +
          (Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
            + ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x)) := by ring
    _ ≤ ((3891854 / 1000000 : ℚ) : ℝ) := hmain
    _ = 3.891854 := by norm_num

end quadrature

/-- LEAF. Wu 2004 page 42 final numerical display, F1.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F1 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 1 ≤ 3.891854 := by
  exact numerical_F1_aux F f ω h hω



/-- LEAF. Wu 2004 page 42 final numerical display, F2.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F2 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 2 ≤ 20.432098 := by
  have hsub := F2_sub_F3 (F := F) (f := f) h ω
  have h3 := numerical_F3_priv F f ω h hω
  have hlog := log_step_F2
  linarith

/-- LEAF. Wu 2004 page 42 final numerical display, F3.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F3 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 3 ≤ 17.327241 := by
  exact numerical_F3_priv F f ω h hω

/-- LEAF. Wu 2004 page 42 final numerical display, F4.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    0.697375 ≤ integralTerms F f ω 4 := by
  sorry

/-- LEAF. Wu 2004 page 42 final numerical display, F5.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    2.118119 ≤ integralTerms F f ω 5 := by
  sorry

end LeanLab.ChenDoubleSieve.Task315
