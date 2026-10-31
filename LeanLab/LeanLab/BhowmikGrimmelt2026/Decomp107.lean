/-
Decomposition of Lemma 7.6 and its written proof on page 29 of P0029.
The original cited declaration is unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Archimedean84
import LeanLab.BhowmikGrimmelt2026.Scaling107
import LeanLab.BhowmikGrimmelt2026.Integration107
import LeanLab.BhowmikGrimmelt2026.Amplitude107
import LeanLab.BhowmikGrimmelt2026.Poisson

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. Page 29 display 7.21. Substitute v = u1 + u2 and sigma = u1 / v. -/
theorem archimedean_coordinates107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {N T : ℝ} (hT : 1 ≤ T) (hTN : T ≤ N)
    (ρ₁ ρ₂ : ℂ) (hρ₁ : 0 < ρ₁.re) (hρ₁' : ρ₁.re ≤ 1)
    (hρ₂ : 0 < ρ₂.re) (hρ₂' : ρ₂.re ≤ 1) :
    Iphi ϕ G N T ρ₁ ρ₂ = ∫ v in Set.Ioi (0 : ℝ),
      (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂ := by
  have hN : 0 < N := by linarith
  let f : ℝ → ℂ := fun u => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ₁ - 1)
  let g : ℝ → ℂ := fun u => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ₂ - 1)
  let h : ℝ → ℂ := fun v => (GT G T (N - v) : ℂ)
  have hz (ρ : ℂ) (u : ℝ) (hu : u ≤ 0) :
      (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ - 1) = 0 := by
    have hzero : ϕ (u / N) = 0 := by
      by_contra hn
      have hs := (hϕ.supp (subset_tsupport ϕ hn)).1
      have : u / N ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hN.le
      linarith
    simp [hzero]
  have hGc : Continuous G := hG.smooth.continuous
  have hh : Continuous h := by dsimp [h, GT]; fun_prop
  have hconv := positive_convolution107 f g h
    (continuous_cutoff_cpow107 hϕ hN ρ₁) (continuous_cutoff_cpow107 hϕ hN ρ₂) hh
    (compact_cutoff_cpow107 hϕ hN ρ₁) (compact_cutoff_cpow107 hϕ hN ρ₂)
    (hz ρ₁) (hz ρ₂)
  calc
    _ = ∫ u in Set.Ioi (0 : ℝ), ∫ w in Set.Ioi (0 : ℝ), f u * g w * h (u + w) := by
      unfold Iphi
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w hw
      dsimp [f, g, h]
      rw [show N - u - w = N - (u + w) by ring]
      push_cast
      ring
    _ = ∫ v in Set.Ioi (0 : ℝ), (∫ u in (0 : ℝ)..v, f u * g (v - u)) * h v := hconv
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      have hinner : (∫ u in (0 : ℝ)..v, f u * g (v - u)) =
          (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * Jphi ϕ N v ρ₁ ρ₂ := by
        rw [← beta_scaling107 ϕ N hv ρ₁ ρ₂]
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [f, g]
        push_cast
        ring
      rw [hinner]
      dsimp [h]
      ring

/-- LEAF. Page 29 proof of 7.19, opposite signs.
Repeated integration by parts in sigma, followed by the outer absolute integral. -/
theorem archimedean_opposite107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → ρ₁.im * ρ₂.im < 0 →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by
  sorry

/-- LEAF. Page 29 proof of 7.19, equal signs including zero.
Repeated integration by parts in v gives decay at scale T / N. -/
theorem archimedean_same107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → 0 ≤ ρ₁.im * ρ₂.im →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) *
          (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A) := by
  sorry

/-- Page 29 proof of 7.20. The normalized dilated kernel is integrable. -/
theorem integrable_GT150 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {T : ℝ} (hT : 0 < T) : Integrable (GT G T) :=
  (GT_contDiff hG.smooth T).continuous.integrable_of_hasCompactSupport
    (GT_hasCompactSupport hG.supp hT)

/-- Page 29 proof of 7.20. The dilated kernel has mass one. -/
theorem integral_GT150 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {T : ℝ} (hT : 0 < T) : (∫ x : ℝ, GT G T x) = 1 := by
  simp [GT, integral_const_mul, Measure.integral_comp_div, abs_of_pos hT,
    hG.integral_one, hT.ne']

/-- Page 29 proof of 7.20. The positive dilation preserves nonnegativity. -/
theorem nonneg_GT150 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {T : ℝ} (hT : 0 < T) (x : ℝ) : 0 ≤ GT G T x :=
  mul_nonneg (inv_nonneg.mpr hT.le) (hG.nonneg _)

/-- Page 29 proof of 7.20. Real base complex powers are measurable at fixed exponent. -/
theorem measurable_real_cpow150 (z : ℂ) : Measurable (fun x : ℝ => (x : ℂ) ^ z) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const x z
    (Or.inr (by simpa using hx))).continuousWithinAt

/-- Page 29 display 7.21. The inner integral is measurable in its outer variable. -/
theorem measurable_Jphi150 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (N : ℝ) (ρ₁ ρ₂ : ℂ) : Measurable (fun v : ℝ => Jphi ϕ N v ρ₁ ρ₂) := by
  have ha : Measurable (fun p : ℝ × ℝ =>
      ((ϕ (p.1 * p.2 / N) * ϕ (p.1 * (1 - p.2) / N) : ℝ) : ℂ)) := by
    have hc := hϕ.smooth.continuous
    fun_prop
  have hb : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (ρ₁ - 1)) :=
    (measurable_real_cpow150 _).comp measurable_snd
  have hc : Measurable (fun p : ℝ × ℝ => ((1 - p.2 : ℝ) : ℂ) ^ (ρ₂ - 1)) :=
    (measurable_real_cpow150 _).comp (measurable_const.sub measurable_snd)
  have hi := (((ha.mul hb).mul hc).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))).measurable
  simpa only [Pi.mul_apply, Jphi, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hi

/-- Page 29 proof of 7.20. Extend the normalized Taylor estimate by zero outside positive v.
The support gap controls the baseline term outside the effective v interval. -/
theorem global_beta_taylor150 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 0 < N → ∀ v : ℝ, ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 →
      ‖(if 0 < v then ((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) * Jphi ϕ N v ρ₁ ρ₂ else 0) -
        Bphi ϕ ρ₁ ρ₂‖ ≤ C * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1| := by
  obtain ⟨CA, hCA, hA⟩ := weighted_beta_taylor107 hϕ
  obtain ⟨CJ, hCJ, hJ⟩ := Jphi_uniform107 hϕ
  refine ⟨CA + 2 * CJ, by positivity, ?_⟩
  intro N hN v ρ₁ ρ₂ h₁ h₁' h₂ h₂'
  have hB : ‖Bphi ϕ ρ₁ ρ₂‖ ≤ CJ := by
    have h := hJ 1 (by norm_num) 1 ρ₁ ρ₂ h₁ h₂
    rwa [Jphi_at_N ϕ (by norm_num)] at h
  by_cases hv : v / N ∈ Set.Icc (2 / 5 : ℝ) (8 / 5)
  · have hv0 : 0 < v := by
      have hh := (le_div_iff₀ hN).mp hv.1
      nlinarith
    rw [if_pos hv0]
    exact (hA N hN v hv ρ₁ ρ₂ h₁ h₁' h₂ h₂').trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : CA ≤ CA + 2 * CJ) (by positivity))
        (abs_nonneg _))
  · have hout : v / N < 2 / 5 ∨ 8 / 5 < v / N := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hv
    have hd : (1 / 2 : ℝ) ≤ |v / N - 1| := by
      rcases hout with hl | hu
      · linarith [neg_le_abs (v / N - 1)]
      · linarith [le_abs_self (v / N - 1)]
    have hz : (if 0 < v then ((v / N : ℝ) : ℂ) ^ (ρ₁ + ρ₂ - 1) *
        Jphi ϕ N v ρ₁ ρ₂ else 0) = 0 := by
      split_ifs
      · rw [Jphi_eq_zero_outside84 hϕ hN (by
          rcases hout with hl | hu
          · exact Or.inl ((div_le_iff₀ hN).mp hl.le)
          · exact Or.inr ((le_div_iff₀ hN).mp hu.le))]
        simp
      · rfl
    rw [hz, zero_sub, norm_neg]
    calc
      _ ≤ CJ := hB
      _ ≤ (2 * CJ) * |v / N - 1| := by nlinarith
      _ ≤ (CA + 2 * CJ) * |v / N - 1| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (CA + 2 * CJ) * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1| := by
        have hf : 1 ≤ 1 + |(ρ₁ + ρ₂).im| := by linarith [abs_nonneg (ρ₁ + ρ₂).im]
        have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ CA + 2 * CJ by positivity)
        exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hm) (abs_nonneg _)

/-- LEAF. Page 29 proof of 7.20.
Normalize by N, extend the cutoff by zero, and integrate against the unit mass kernel. -/
theorem archimedean_taylor107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → |(ρ₁ + ρ₂).im| * T ≤ N →
      ‖(∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂) -
          Bphi ϕ ρ₁ ρ₂ * (N : ℂ) ^ (ρ₁ + ρ₂ - 1)‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + |(ρ₁ + ρ₂).im|) * T / N := by
  obtain ⟨C, hC, hbound⟩ := global_beta_taylor150 hϕ
  refine ⟨2 * C, ?_⟩
  intro N T hT hTN ρ₁ ρ₂ h₁ h₁' h₂ h₂' _hfreq
  have hT0 : 0 < T := by linarith
  have hN : 0 < N := by linarith
  let z : ℂ := ρ₁ + ρ₂ - 1
  let B : ℂ := Bphi ϕ ρ₁ ρ₂
  let F : ℝ → ℂ := fun v =>
    if 0 < v then ((v / N : ℝ) : ℂ) ^ z * Jphi ϕ N v ρ₁ ρ₂ else 0
  let k : ℝ → ℝ := fun v => GT G T (N - v)
  let D : ℝ := 2 * C * (1 + |(ρ₁ + ρ₂).im|) * T / N
  have hk : Integrable k := (integrable_GT150 hG hT0).comp_sub_left N
  have hkn (v : ℝ) : 0 ≤ k v := nonneg_GT150 hG hT0 _
  have hki : (∫ v : ℝ, k v) = 1 := by
    dsimp [k]
    rw [integral_sub_left_eq_self (GT G T) volume N, integral_GT150 hG hT0]
  have hFm : Measurable F := by
    dsimp [F]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (((measurable_real_cpow150 z).comp (measurable_id.div_const N)).mul
        (measurable_Jphi150 hϕ N ρ₁ ρ₂)) measurable_const
  have hkm : Measurable k := by
    have hc := (GT_contDiff hG.smooth T).continuous
    exact (hc.comp (continuous_const.sub continuous_id)).measurable
  have hpoint (v : ℝ) : ‖(F v - B) * (k v : ℂ)‖ ≤ D * k v := by
    by_cases hz : k v = 0
    · simp [hz]
    have hdist : |N - v| ≤ 2 * T := by
      by_contra hh
      exact hz (GT_eq_zero hG.supp hT0 (lt_of_not_ge hh))
    have hdist' : |v / N - 1| ≤ 2 * T / N := by
      rw [show v / N - 1 = -(N - v) / N by field_simp [hN.ne']; ring, abs_div, abs_neg, abs_of_pos hN]
      exact div_le_div_of_nonneg_right hdist hN.le
    have he := hbound N hN v ρ₁ ρ₂ h₁ h₁' h₂ h₂'
    change ‖F v - B‖ ≤ C * (1 + |(ρ₁ + ρ₂).im|) * |v / N - 1| at he
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hkn v)]
    calc
      _ ≤ (C * (1 + |(ρ₁ + ρ₂).im|) * (2 * T / N)) * k v :=
        mul_le_mul_of_nonneg_right
          (he.trans (mul_le_mul_of_nonneg_left hdist' (by positivity))) (hkn v)
      _ = D * k v := by dsimp [D]; ring
  have herror : Integrable (fun v : ℝ => (F v - B) * (k v : ℂ)) :=
    (hk.const_mul D).mono'
      ((hFm.sub measurable_const).mul (Complex.continuous_ofReal.measurable.comp hkm)).aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hbase : Integrable (fun v : ℝ => B * (k v : ℂ)) := hk.ofReal.const_mul B
  have hF : Integrable (fun v : ℝ => F v * (k v : ℂ)) := by
    convert herror.add hbase using 1
    ext v
    simp only [Pi.add_apply]
    ring
  have hbaseint : (∫ v : ℝ, B * (k v : ℂ)) = B := by
    have hcast : (∫ v : ℝ, (k v : ℂ)) = Complex.ofReal (∫ v : ℝ, k v) := integral_ofReal
    rw [integral_const_mul, hcast, hki]
    simp
  have hdiff : (∫ v : ℝ, F v * (k v : ℂ)) - B =
      ∫ v : ℝ, (F v - B) * (k v : ℂ) := by
    calc
      _ = (∫ v : ℝ, F v * (k v : ℂ)) - (∫ v : ℝ, B * (k v : ℂ)) := by rw [hbaseint]
      _ = ∫ v : ℝ, F v * (k v : ℂ) - B * (k v : ℂ) := (integral_sub hF hbase).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with v
        ring
  have herr : ‖(∫ v : ℝ, F v * (k v : ℂ)) - B‖ ≤ D := by
    rw [hdiff]
    have hi := norm_integral_le_of_norm_le (hk.const_mul D) (Filter.Eventually.of_forall hpoint)
    simpa only [integral_const_mul, hki, mul_one] using hi
  have houter : (∫ v in Set.Ioi (0 : ℝ),
      (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂) =
      (N : ℂ) ^ z * ∫ v : ℝ, F v * (k v : ℂ) := by
    calc
      _ = ∫ v in Set.Ioi (0 : ℝ), (N : ℂ) ^ z * (F v * (k v : ℂ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        have hp : (v : ℂ) ^ z = (N : ℂ) ^ z * ((v / N : ℝ) : ℂ) ^ z := by
          calc
            _ = ((N * (v / N) : ℝ) : ℂ) ^ z := by rw [mul_div_cancel₀ v hN.ne']
            _ = _ := by
              simpa only [Complex.ofReal_mul] using
                Complex.mul_cpow_ofReal_nonneg hN.le (div_nonneg (show 0 ≤ v from hv.le) hN.le) z
        dsimp [F, k]
        rw [if_pos (show 0 < v from hv)]
        change (v : ℂ) ^ z * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂ = _
        rw [hp]
        ring
      _ = ∫ v : ℝ, (N : ℂ) ^ z * (F v * (k v : ℂ)) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro v hv
        have hv' : ¬ 0 < v := by simpa using hv
        simp [F, hv']
      _ = _ := integral_const_mul _ _
  rw [houter]
  change ‖(N : ℂ) ^ z * (∫ v : ℝ, F v * (k v : ℂ)) - B * (N : ℂ) ^ z‖ ≤ _
  rw [show (N : ℂ) ^ z * (∫ v : ℝ, F v * (k v : ℂ)) - B * (N : ℂ) ^ z =
    (N : ℂ) ^ z * ((∫ v : ℝ, F v * (k v : ℂ)) - B) by ring,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN]
  calc
    _ ≤ N ^ z.re * D := mul_le_mul_of_nonneg_left herr (Real.rpow_nonneg hN.le _)
    _ = _ := by dsimp [D, z]; ring

/-- LEAF. Page 29 proof of 7.19. The unscaled decay is stronger since T is at most N. -/
theorem archimedean_decay_compare107 {A N T U : ℝ} (hA : 0 < A)
    (hT : 1 ≤ T) (hTN : T ≤ N) (hU : 0 ≤ U) :
    (1 + U) ^ (-A) ≤ (1 + U * T / N) ^ (-A) := by
  have hN : 0 < N := by linarith
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  have : U * T / N ≤ U := (div_le_iff₀ hN).mpr (mul_le_mul_of_nonneg_left hTN hU)
  linarith

/-- CONDITIONAL on the two remaining oscillatory leaves above. Exact existing Lemma76 proposition.
The assembly has no direct sorry and does not invoke the original cited lemma76. -/
theorem lemma76_decomposed107 : Lemma76 := by
  intro ϕ G hϕ hG
  constructor
  · intro A hA
    obtain ⟨C₁, hC₁⟩ := archimedean_opposite107 hϕ hG A hA
    obtain ⟨C₂, hC₂⟩ := archimedean_same107 hϕ hG A hA
    refine ⟨max (max C₁ C₂) 0, ?_⟩
    intro N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂'
    rw [archimedean_coordinates107 hϕ hG hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂']
    have hN : 0 < N := by linarith
    have hpow : 0 ≤ N ^ ((ρ₁ + ρ₂).re - 1) := Real.rpow_nonneg (by linarith) _
    by_cases hs : ρ₁.im * ρ₂.im < 0
    · have hb := hC₁ N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs
      apply hb.trans
      have hc : C₁ ≤ max (max C₁ C₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
      calc
        C₁ * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) ≤
            max (max C₁ C₂) 0 * N ^ ((ρ₁ + ρ₂).re - 1) *
              (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by
          gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (archimedean_decay_compare107 hA hT hTN (by positivity))
          (mul_nonneg (le_max_right _ _) hpow)
    · exact (hC₂ N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' (le_of_not_gt hs)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (le_trans (le_max_right C₁ C₂) (le_max_left _ _)) hpow)
          (Real.rpow_nonneg (by positivity) _))
  · obtain ⟨C, hC⟩ := archimedean_taylor107 hϕ hG
    refine ⟨C, ?_⟩
    intro N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs
    rw [archimedean_coordinates107 hϕ hG hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂']
    exact hC N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_coordinates107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_opposite107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_same107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_taylor107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_decay_compare107
#print axioms LeanLab.BhowmikGrimmelt2026.lemma76_decomposed107

#print axioms LeanLab.BhowmikGrimmelt2026.integrable_GT150
#print axioms LeanLab.BhowmikGrimmelt2026.integral_GT150
#print axioms LeanLab.BhowmikGrimmelt2026.nonneg_GT150
#print axioms LeanLab.BhowmikGrimmelt2026.measurable_real_cpow150

#print axioms LeanLab.BhowmikGrimmelt2026.measurable_Jphi150
#print axioms LeanLab.BhowmikGrimmelt2026.global_beta_taylor150
