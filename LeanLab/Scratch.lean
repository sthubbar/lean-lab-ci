import LeanLab.BhowmikGrimmelt2026.Decomp107

open MeasureTheory
namespace LeanLab.BhowmikGrimmelt2026

private lemma test_power_bound {N v r : ℝ} (hN : 1 ≤ N)
    (hvlo : (2 / 5 : ℝ) * N ≤ v) (hvhi : v ≤ 2 * N)
    (hrlo : -1 ≤ r) (hrhi : r ≤ 1) : v ^ r ≤ 5 * N ^ r := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hbase0 : 0 < (2 / 5 : ℝ) * N := by positivity
  have hv0 : 0 < v := lt_of_lt_of_le hbase0 hvlo
  by_cases hr0 : r ≤ 0
  · have hbase : (2 / 5 : ℝ) * N ≤ v := hvlo
    have h1 : v ^ r ≤ ((2 / 5 : ℝ) * N) ^ r :=
      Real.rpow_le_rpow_of_nonpos hbase0 hbase hr0
    have hmul : ((2 / 5 : ℝ) * N) ^ r = (2 / 5 : ℝ) ^ r * N ^ r := by
      rw [Real.mul_rpow (by norm_num) (le_of_lt hN0)]
    have hb : (2 / 5 : ℝ) ^ r ≤ 5 := by
      have hinv : (2 / 5 : ℝ) ^ r = (5 / 2 : ℝ) ^ (-r) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2 / 5) r,
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5 / 2) (-r)]
        congr 1
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_inv (by norm_num)]
        ring
      have hp := Real.rpow_le_rpow (x := (5 / 2 : ℝ)) (y := (5 / 2 : ℝ)) (z := -r)
        (by norm_num) (by linarith : -r ≤ 1) (by linarith : 0 ≤ -r)
      rw [Real.rpow_one] at hp
      rw [hinv]
      linarith
    calc
      v ^ r ≤ ((2 / 5 : ℝ) * N) ^ r := h1
      _ = (2 / 5 : ℝ) ^ r * N ^ r := hmul
      _ ≤ 5 * N ^ r := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hN0.le r)
  · have hr0' : 0 ≤ r := le_of_not_ge hr0
    have h1 : v ^ r ≤ (2 * N) ^ r := Real.rpow_le_rpow hv0.le hvhi hr0'
    have hmul : (2 * N) ^ r = 2 ^ r * N ^ r := by
      rw [Real.mul_rpow (by norm_num) (le_of_lt hN0)]
    have hb : 2 ^ r ≤ 2 := by
      have hp := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (y := r) (z := 1)
        (by norm_num : (1 : ℝ) ≤ 2) (by linarith : r ≤ 1)
      rw [Real.rpow_one] at hp
      exact hp
    calc
      v ^ r ≤ (2 * N) ^ r := h1
      _ = 2 ^ r * N ^ r := hmul
      _ ≤ 2 * N ^ r := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hN0.le r)

private theorem test_plain {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) := by
  obtain ⟨CJ, hCJ, hJ⟩ := Jphi_uniform107 hϕ
  refine ⟨5 * CJ, by positivity, ?_⟩
  intro N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂'
  have hN : 1 ≤ N := hT.trans hTN
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let z : ℂ := ρ₁ + ρ₂ - 1
  let k : ℝ → ℝ := fun v => GT G T (N - v)
  let F : ℝ → ℂ := fun v =>
    if 0 < v then (v : ℂ) ^ z * (k v : ℂ) * Jphi ϕ N v ρ₁ ρ₂ else 0
  have hk : Integrable k := (integrable_GT150 hG hT0).comp_sub_left N
  have hkn (v : ℝ) : 0 ≤ k v := nonneg_GT150 hG hT0 _
  have hki : (∫ v : ℝ, k v) = 1 := by
    dsimp [k]
    rw [integral_sub_left_eq_self (GT G T) volume N, integral_GT150 hG hT0]
  have hkm : Measurable k := by
    have hc := (GT_contDiff hG.smooth T).continuous
    exact (hc.comp (continuous_const.sub continuous_id)).measurable
  have hFm : Measurable F := by
    dsimp [F]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (((measurable_real_cpow150 z).comp measurable_id).mul
        ((Complex.continuous_ofReal.measurable.comp hkm).mul
          (measurable_Jphi150 hϕ N ρ₁ ρ₂))) measurable_const
  have hr : -1 ≤ z.re ∧ z.re ≤ 1 := by
    dsimp [z]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    constructor <;> linarith
  have hpoint (v : ℝ) : ‖F v‖ ≤ 5 * N ^ z.re * CJ * k v := by
    by_cases hv0 : 0 < v
    · by_cases hout : v ≤ (2 / 5 : ℝ) * N ∨ (8 / 5 : ℝ) * N ≤ v
      · have hz := Jphi_eq_zero_outside84 hϕ (lt_of_lt_of_le zero_lt_one hN) hout ρ₁ ρ₂
        simp [F, hv0, hz]
      · have hvin : (2 / 5 : ℝ) * N < v ∧ v < (8 / 5 : ℝ) * N := by
          simpa only [not_le, not_or] using hout
        have hvhi : v ≤ 2 * N := by linarith
        have hp := test_power_bound hN hvin.1.le hvhi hr.1 hr.2
        rw [F, if_pos hv0, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hkn v)]
        calc
          ‖(v : ℂ) ^ z‖ * ‖(k v : ℂ)‖ * ‖Jphi ϕ N v ρ₁ ρ₂‖ ≤
              5 * N ^ z.re * k v * CJ := by
                gcongr
                · exact hp
                · exact (hJ N (lt_of_lt_of_le zero_lt_one hN) v ρ₁ ρ₂ hρ₁ hρ₂).le
          _ = 5 * N ^ z.re * CJ * k v := by ring
    · simp [F, hv0]
  have hF : Integrable F := by
    have hupper : Integrable (fun v : ℝ => 5 * N ^ z.re * CJ * k v) := by
      simpa using (hk.const_mul (5 * N ^ z.re * CJ))
    refine hupper.mono' ?_
    filter_upwards [] with v
    rw [hpoint v]
  have houter : (∫ v in Set.Ioi (0 : ℝ),
      (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂) =
      ∫ v : ℝ, F v := by
    calc
      _ = ∫ v in Set.Ioi (0 : ℝ),
          (v : ℂ) ^ z * (k v : ℂ) * Jphi ϕ N v ρ₁ ρ₂ := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro v hv
            dsimp [z, k]
      _ = ∫ v : ℝ, F v := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro v hv
        have hv' : ¬ 0 < v := by simpa using hv
        simp [F, hv']
  rw [houter]
  have hi := norm_integral_le_of_norm_le hF (Filter.Eventually.of_forall hpoint)
  calc
    ‖∫ v : ℝ, F v‖ ≤ ∫ v : ℝ, ‖F v‖ := hi
    _ ≤ ∫ v : ℝ, 5 * N ^ z.re * CJ * k v := by
      apply integral_mono_ae
      filter_upwards [] with v
      exact hpoint v
    _ = 5 * N ^ z.re * CJ := by
      rw [integral_const_mul, integral_const_mul, hki]
      norm_num
    _ = 5 * CJ * N ^ z.re := by ring

end LeanLab.BhowmikGrimmelt2026
