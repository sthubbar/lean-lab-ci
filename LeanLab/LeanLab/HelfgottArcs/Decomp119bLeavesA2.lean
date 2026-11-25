/-
P0013 pages 74 and 75, the compact range of Lemma A.2, split along the paper's own proof:
interpolation bound A.4, second derivative bound from A.5, and the sampled grid with step 0.001.
AI wrote the Lean code for burst-20261122 S92. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.FourierDecay

namespace LeanLab.HelfgottArcs.Decomp119bLeavesA2
open MeasureTheory Set Real

/-! Helper lemmas for the leaves below, proved by AI for S124 burst-20261122. -/

open scoped FourierTransform


theorem a2h_diff2 {A : ℝ → ℂ} (hA : ContDiff ℝ 2 A) : Differentiable ℝ A ∧ Differentiable ℝ (deriv A) := by
  have h : ContDiff ℝ (1 + 1) A := hA
  obtain ⟨h1, -, h2⟩ := contDiff_succ_iff_deriv.mp h
  exact ⟨h1, h2.differentiable (by norm_num)⟩

theorem a2h_taylor_right (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (M t s : ℝ) (hts : t ≤ s)
    (hM : ∀ v ∈ Icc t s, ‖deriv (deriv g) v‖ ≤ M) :
    ‖g s - g t - ((s - t : ℝ) : ℂ) * deriv g t‖ ≤ M / 2 * (s - t) ^ 2 := by
  obtain ⟨h1, h2⟩ := a2h_diff2 hg
  have hk' := norm_image_sub_le_of_norm_deriv_le_segment' (f := deriv g)
    (f' := deriv (deriv g)) (a := t) (b := s) (C := M)
    (fun x _ => (h2 x).hasDerivAt.hasDerivWithinAt) (fun x hx => hM x (Ico_subset_Icc_self hx))
  have hd : ∀ x, HasDerivAt (fun x : ℝ => g x - g t - ((x - t : ℝ) : ℂ) * deriv g t)
      (deriv g x - deriv g t) x := by
    intro x
    have := ((h1 x).hasDerivAt.sub_const (g t)).sub
      ((((hasDerivAt_id x).sub_const t).ofReal_comp).mul_const (deriv g t))
    exact this.congr_deriv (by simp)
  have hB : ∀ x, HasDerivAt (fun x : ℝ => M / 2 * (x - t) ^ 2) (M * (x - t)) x := by
    intro x
    have := (((hasDerivAt_id x).sub_const t).pow 2).const_mul (M / 2)
    exact this.congr_deriv (by simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]; ring)
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun x : ℝ => g x - g t - ((x - t : ℝ) : ℂ) * deriv g t)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt) (by simp) hB
    (fun x hx => hk' x (Ico_subset_Icc_self hx)) (x := s) ⟨hts, le_rfl⟩
  simpa using this

theorem a2h_taylor_left (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (M a t : ℝ) (hat : a ≤ t)
    (hM : ∀ v ∈ Icc a t, ‖deriv (deriv g) v‖ ≤ M) :
    ‖g a - g t - ((a - t : ℝ) : ℂ) * deriv g t‖ ≤ M / 2 * (t - a) ^ 2 := by
  have hd1 : deriv (fun x => g (-x)) = fun x => -deriv g (-x) := funext fun x => deriv_comp_neg g x
  have hd2 : ∀ v, deriv (deriv (fun x => g (-x))) v = deriv (deriv g) (-v) := by
    intro v
    rw [hd1, deriv.fun_neg, deriv_comp_neg (deriv g) v, neg_neg]
  have := a2h_taylor_right (fun x => g (-x)) (hg.comp contDiff_neg) M (-t) (-a) (by linarith)
    (by
      intro v hv
      rw [hd2]
      exact hM (-v) ⟨by linarith [hv.2], by linarith [hv.1]⟩)
  rw [hd1] at this
  simp only [neg_neg] at this
  convert this using 2
  · push_cast; ring
  · ring



theorem a2h_fourier_piece (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) (t : ℝ) :
    𝓕 ((Set.indicator (Ioc a b) (fun x : ℝ => ((g x : ℝ) : ℂ)))) t = ∫ x in a..b, e (-(x * t)) * (g x : ℂ) := by
  rw [Real.fourier_real_eq, intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
  congr 1
  funext x
  simp only [Set.indicator]
  split_ifs
  · rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, e]
    congr 2
    push_cast; ring
  · simp

theorem a2h_integrable_pow_piece (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b))
    (n : ℕ) : Integrable (fun x : ℝ => x ^ n • (Set.indicator (Ioc a b) (fun x : ℝ => ((g x : ℝ) : ℂ))) x) := by
  have : (fun x : ℝ => x ^ n • (Set.indicator (Ioc a b) (fun x : ℝ => ((g x : ℝ) : ℂ))) x) =
      Set.indicator (Ioc a b) (fun x => x ^ n • (g x : ℂ)) := by
    funext x; simp only [Set.indicator]; split_ifs <;> simp
  rw [this]
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioc
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  exact (continuousOn_pow n).smul (Complex.continuous_ofReal.comp_continuousOn hg)

theorem a2h_contDiff_fourier_piece (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b)) :
    ContDiff ℝ 2 (𝓕 ((Set.indicator (Ioc a b) (fun x : ℝ => ((g x : ℝ) : ℂ))))) := by
  apply Real.contDiff_fourier
  intro n _
  convert (a2h_integrable_pow_piece a b hab g hg n).norm using 1
  funext x; simp [norm_smul]

theorem a2h_deriv2_fourier_piece (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b)) :
    deriv (deriv (𝓕 ((Set.indicator (Ioc a b) (fun x : ℝ => ((g x : ℝ) : ℂ)))))) =
      𝓕 (fun x : ℝ => (-2 * π * Complex.I * x) ^ 2 • (Set.indicator (Ioc a b) (fun x : ℝ => ((g x : ℝ) : ℂ))) x) := by
  have := Real.iteratedDeriv_fourier (N := 2) (n := 2)
    (fun n _ => a2h_integrable_pow_piece a b hab g hg n) le_rfl
  rw [← this, iteratedDeriv_succ, iteratedDeriv_one]

theorem a2h_norm_fourier_le_of_le (K : ℝ → ℂ) (B : ℝ → ℝ) (hK : Integrable K) (hB : Integrable B)
    (h : ∀ x, ‖K x‖ ≤ B x) (t : ℝ) : ‖𝓕 K t‖ ≤ ∫ x, B x := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono (by simp only [Circle.norm_smul]; exact hK.norm) hB ?_
  intro x; simp only [Circle.norm_smul]; exact h x

theorem a2h_norm_deriv2_fourier_piece (a b C : ℝ) (hab : a ≤ b) (ha : 0 < a) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc a b)) (hC : ∀ x ∈ Ioc a b, x ^ 2 * |g x| ≤ C) (t : ℝ) :
    ‖deriv (deriv (𝓕 ((Set.indicator (Ioc a b) (fun x : ℝ => ((g x : ℝ) : ℂ)))))) t‖ ≤ 4 * π ^ 2 * C * (b - a) := by
  rw [a2h_deriv2_fourier_piece a b hab g hg]
  have hK : Integrable (fun x : ℝ => (-2 * π * Complex.I * x) ^ 2 • (Set.indicator (Ioc a b) (fun x : ℝ => ((g x : ℝ) : ℂ))) x) := by
    have := (a2h_integrable_pow_piece a b hab g hg 2).smul ((-2 * π * Complex.I) ^ 2)
    convert this using 1
    funext x; simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]; push_cast; ring
  have hB : Integrable (Set.indicator (Ioc a b) (fun _ : ℝ => 4 * π ^ 2 * C)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  refine (a2h_norm_fourier_le_of_le _ _ hK hB ?_ t).trans_eq ?_
  · intro x
    simp only [Set.indicator]
    split_ifs with hx
    · rw [smul_eq_mul, norm_mul, norm_pow]
      have : ‖-2 * π * Complex.I * (x : ℂ)‖ = 2 * π * |x| := by
        simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
      rw [this, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      have := hC x hx
      nlinarith [pi_pos, sq_nonneg π]
    · simp
  · rw [integral_indicator measurableSet_Ioc, setIntegral_const]
    simp [hab]
    ring

theorem a2h_deriv2_e (δ t : ℝ) :
    deriv (deriv (fun s : ℝ => e (-(s * δ)))) t =
      (-2 * π * Complex.I * (δ : ℂ)) ^ 2 * e (-(t * δ)) := by
  have h1 : deriv (fun s : ℝ => e (-(s * δ))) =
      fun t => (-2 * π * Complex.I * (δ : ℂ)) * e (-(t * δ)) :=
    funext fun t => (hasDerivAt_e_neg_mul δ t).deriv
  rw [h1, ((hasDerivAt_e_neg_mul δ t).const_mul (-2 * π * Complex.I * (δ : ℂ))).deriv]
  ring

theorem a2h_contDiff_e (δ : ℝ) : ContDiff ℝ 2 (fun s : ℝ => e (-(s * δ))) := by
  have h : ContDiff ℝ 2 (fun s : ℝ => ((-(s * δ) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_id.mul contDiff_const).neg)
  exact Complex.contDiff_exp.comp (contDiff_const.mul h)


theorem a2h_cont_g (c a b : ℝ) (ha : 0 < a) : ContinuousOn (fun x : ℝ => c / x ^ 2) (Icc a b) := by
  refine continuousOn_const.div (continuousOn_id.pow 2) ?_
  intro t ht; exact pow_ne_zero 2 (by linarith [ht.1])

theorem a2h_F_eq : (fun t : ℝ => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t) =
    fun t => (16 * e (-(t * (1 / 4))) - 16 * e (-(t * (1 / 2))) + 4 * e (-(t * 1))) +
      𝓕 (Set.indicator (Ioc (1 / 4) (1 / 2)) (fun x : ℝ => (((-4 / x ^ 2 : ℝ)) : ℂ))) t + 𝓕 (Set.indicator (Ioc (1 / 2) 1) (fun x : ℝ => (((4 / x ^ 2 : ℝ)) : ℂ))) t := by
  funext t
  rw [sq_mul_fhat_eta2_eq, a2h_fourier_piece _ _ (by norm_num), a2h_fourier_piece _ _ (by norm_num)]
  rw [show -t / 4 = -(t * (1 / 4)) by ring, show -t / 2 = -(t * (1 / 2)) by ring,
    show -t = -(t * 1) by ring]
  beta_reduce
  ring

/-- LEAF: P0013 page 74 display A.4, maximum of a C2 function on an interval from its endpoints.
Class MEDIUM. P0013 display A.4, applied on page 75 to 4g plus fhat. Linear interpolation plus
the Taylor remainder bound, valued in the complex numbers. -/
theorem interp_A4 (g : ℝ → ℂ) (M a b : ℝ) (hab : a ≤ b) (hg : ContDiff ℝ 2 g)
    (hM : ∀ v ∈ Icc a b, ‖deriv (deriv g) v‖ ≤ M) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖g t‖ ≤ max ‖g a‖ ‖g b‖ + (b - a) ^ 2 / 8 * M := by
  obtain ⟨hat, htb⟩ := ht
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  rcases eq_or_lt_of_le hab with hEq | hlt
  · subst hEq
    have : t = a := le_antisymm htb hat
    subst this
    have := le_max_left ‖g t‖ ‖g t‖
    nlinarith
  have R1 := a2h_taylor_left g hg M a t hat (fun v hv => hM v ⟨hv.1, hv.2.trans htb⟩)
  have R2 := a2h_taylor_right g hg M t b htb (fun v hv => hM v ⟨hat.trans hv.1, hv.2⟩)
  set r1 := g a - g t - ((a - t : ℝ) : ℂ) * deriv g t
  set r2 := g b - g t - ((b - t : ℝ) : ℂ) * deriv g t
  have key : ((b - a : ℝ) : ℂ) * g t =
      ((b - t : ℝ) : ℂ) * g a + ((t - a : ℝ) : ℂ) * g b - ((b - t : ℝ) : ℂ) * r1 -
        ((t - a : ℝ) : ℂ) * r2 := by
    simp only [r1, r2]; push_cast; ring
  have hn : ‖((b - a : ℝ) : ℂ) * g t‖ = ‖((b - t : ℝ) : ℂ) * g a + ((t - a : ℝ) : ℂ) * g b -
      ((b - t : ℝ) : ℂ) * r1 - ((t - a : ℝ) : ℂ) * r2‖ := by rw [key]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hn
  have hle : (b - a) * ‖g t‖ ≤ (b - t) * ‖g a‖ + (t - a) * ‖g b‖ + (b - t) * ‖r1‖ +
      (t - a) * ‖r2‖ := by
    rw [hn]
    have n1 := norm_sub_le (((b - t : ℝ) : ℂ) * g a + ((t - a : ℝ) : ℂ) * g b -
      ((b - t : ℝ) : ℂ) * r1) (((t - a : ℝ) : ℂ) * r2)
    have n2 := norm_sub_le (((b - t : ℝ) : ℂ) * g a + ((t - a : ℝ) : ℂ) * g b)
      (((b - t : ℝ) : ℂ) * r1)
    have n3 := norm_add_le (((b - t : ℝ) : ℂ) * g a) (((t - a : ℝ) : ℂ) * g b)
    have c1 : ‖((b - t : ℝ) : ℂ)‖ = b - t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have c2 : ‖((t - a : ℝ) : ℂ)‖ = t - a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    simp only [norm_mul, c1, c2] at n1 n2 n3
    linarith
  have hA := le_max_left ‖g a‖ ‖g b‖
  have hBm := le_max_right ‖g a‖ ‖g b‖
  set m := max ‖g a‖ ‖g b‖
  have h1 : (b - t) * ‖g a‖ + (t - a) * ‖g b‖ ≤ (b - a) * m := by
    nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : 0 ≤ b - t),
      mul_le_mul_of_nonneg_left hBm (by linarith : 0 ≤ t - a)]
  have h2 : (b - t) * ‖r1‖ + (t - a) * ‖r2‖ ≤ (b - a) * ((b - a) ^ 2 / 8 * M) := by
    have e1 := mul_le_mul_of_nonneg_left R1 (by linarith : 0 ≤ b - t)
    have e2 := mul_le_mul_of_nonneg_left R2 (by linarith : 0 ≤ t - a)
    have : (b - t) * (M / 2 * (t - a) ^ 2) + (t - a) * (M / 2 * (b - t) ^ 2) ≤
        (b - a) * ((b - a) ^ 2 / 8 * M) := by
      have hq : (t - a) * (b - t) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * t - a - b)]
      have : (b - t) * (M / 2 * (t - a) ^ 2) + (t - a) * (M / 2 * (b - t) ^ 2) =
          M / 2 * (b - a) * ((t - a) * (b - t)) := by ring
      rw [this]
      have : 0 ≤ M / 2 * (b - a) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hq this]
    linarith
  have : (b - a) * ‖g t‖ ≤ (b - a) * (m + (b - a) ^ 2 / 8 * M) := by nlinarith
  exact le_of_mul_le_mul_left this (by linarith)


/-- LEAF: P0013 page 75, smoothness of the multiplier 4g plus fhat, the Fourier transform of a
compactly supported bounded weight. Class MEDIUM. P0013 page 75, needed to apply display A.4. -/
theorem a2_contDiff :
    ContDiff ℝ 2 (fun t : ℝ => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t) := by
  rw [a2h_F_eq]
  have hAc := a2h_contDiff_fourier_piece (1 / 4) (1 / 2) (by norm_num) (fun x : ℝ => -4 / x ^ 2) (a2h_cont_g _ _ _ (by norm_num))
  have hBc := a2h_contDiff_fourier_piece (1 / 2) 1 (by norm_num) (fun x : ℝ => 4 / x ^ 2) (a2h_cont_g _ _ _ (by norm_num))
  exact ((((contDiff_const.mul (a2h_contDiff_e _)).sub (contDiff_const.mul (a2h_contDiff_e _))).add
    (contDiff_const.mul (a2h_contDiff_e _))).add hAc).add hBc


/-- LEAF: P0013 page 75, the bound by 48 pi squared on the second derivative of 4g plus fhat,
from display A.5 and the bound 12 pi squared for fhat second derivative. Class HARD. P0013
page 75 after display A.8. -/
theorem a2_second_deriv (v : ℝ) :
    ‖deriv (deriv (fun t : ℝ => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t)) v‖ ≤
      48 * π ^ 2 := by
  rw [a2h_F_eq]
  set A := 𝓕 (Set.indicator (Ioc (1 / 4) (1 / 2)) (fun x : ℝ => (((-4 / x ^ 2 : ℝ)) : ℂ)))
  set B := 𝓕 (Set.indicator (Ioc (1 / 2) 1) (fun x : ℝ => (((4 / x ^ 2 : ℝ)) : ℂ)))
  have hA := a2h_diff2 (a2h_contDiff_fourier_piece (1 / 4) (1 / 2) (by norm_num) (fun x : ℝ => -4 / x ^ 2) (a2h_cont_g _ _ _ (by norm_num)))
  have hB := a2h_diff2 (a2h_contDiff_fourier_piece (1 / 2) 1 (by norm_num) (fun x : ℝ => 4 / x ^ 2) (a2h_cont_g _ _ _ (by norm_num)))
  set E : ℝ → ℝ → ℂ := fun δ s => e (-(s * δ)) with hE
  have hE1 (δ : ℝ) : Differentiable ℝ (E δ) :=
    (a2h_contDiff_e δ).differentiable (by norm_num)
  have hE2 (δ : ℝ) : Differentiable ℝ (deriv (E δ)) :=
    (a2h_diff2 (a2h_contDiff_e δ)).2
  have hd1 : deriv (fun t => (16 * E (1 / 4) t - 16 * E (1 / 2) t + 4 * E 1 t) + A t + B t) =
      fun t => (16 * deriv (E (1 / 4)) t - 16 * deriv (E (1 / 2)) t + 4 * deriv (E 1) t) +
        deriv A t + deriv B t := by
    funext t
    exact (((((hE1 _ t).hasDerivAt.const_mul 16).sub ((hE1 _ t).hasDerivAt.const_mul 16)).add
      ((hE1 _ t).hasDerivAt.const_mul 4)).add (hA.1 t).hasDerivAt |>.add (hB.1 t).hasDerivAt).deriv
  change ‖deriv (deriv (fun t => (16 * E (1 / 4) t - 16 * E (1 / 2) t + 4 * E 1 t) + A t + B t)) v‖ ≤ _
  have hd2 : HasDerivAt (fun t => (16 * deriv (E (1 / 4)) t - 16 * deriv (E (1 / 2)) t +
      4 * deriv (E 1) t) + deriv A t + deriv B t)
      ((16 * deriv (deriv (E (1 / 4))) v - 16 * deriv (deriv (E (1 / 2))) v +
        4 * deriv (deriv (E 1)) v) + deriv (deriv A) v + deriv (deriv B) v) v :=
    ((((hE2 _ v).hasDerivAt.const_mul 16).sub ((hE2 _ v).hasDerivAt.const_mul 16)).add
      ((hE2 _ v).hasDerivAt.const_mul 4)).add (hA.2 v).hasDerivAt |>.add (hB.2 v).hasDerivAt
  rw [hd1, hd2.deriv]
  have hJ (δ : ℝ) : ‖deriv (deriv (E δ)) v‖ = 4 * π ^ 2 * δ ^ 2 := by
    rw [hE, a2h_deriv2_e, norm_mul, norm_e, norm_pow]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos, mul_pow, sq_abs]
    norm_num
  have hAb := a2h_norm_deriv2_fourier_piece (1 / 4) (1 / 2) 4 (by norm_num) (by norm_num) (fun x : ℝ => -4 / x ^ 2)
    (a2h_cont_g _ _ _ (by norm_num)) (by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      simp only [abs_div, abs_neg]
      rw [abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos (by positivity)]
      field_simp; rfl) v
  have hBb := a2h_norm_deriv2_fourier_piece (1 / 2) 1 4 (by norm_num) (by norm_num) (fun x : ℝ => 4 / x ^ 2)
    (a2h_cont_g _ _ _ (by norm_num)) (by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      simp only [abs_div]
      rw [abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos (by positivity)]
      field_simp; rfl) v
  have h1 := hJ (1 / 4); have h2 := hJ (1 / 2); have h3 := hJ 1
  calc _ ≤ ‖16 * deriv (deriv (E (1 / 4))) v - 16 * deriv (deriv (E (1 / 2))) v +
        4 * deriv (deriv (E 1)) v‖ + ‖deriv (deriv A) v‖ + ‖deriv (deriv B) v‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (16 * ‖deriv (deriv (E (1 / 4))) v‖ + 16 * ‖deriv (deriv (E (1 / 2))) v‖ +
        4 * ‖deriv (deriv (E 1)) v‖) + ‖deriv (deriv A) v‖ + ‖deriv (deriv B) v‖ := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
        · simp [norm_mul]
        · simp [norm_mul]
    _ ≤ 48 * π ^ 2 := by rw [h1, h2, h3]; linarith


/-- LEAF: P0013 page 75, the Simpson rule grid check at t equal to k over 1000, largest value
31.52065 with error at most 0.000045. Class HARD. P0013 page 75, numerical certificate; the
floating point reproduction is gen/task81_lemma_a2.py, not a proof. -/
theorem a2_grid_certificate (k : ℕ) (hk : k ≤ 655000) :
    ‖(-2 * π * Complex.I * ((k / 1000 : ℝ) : ℂ)) ^ 2 * fhat eta2 (k / 1000 : ℝ)‖ ≤ 31.520695 := by
  sorry

/-- Interpolation step on one grid cell, assembled from A.4 and the second derivative bound. -/
theorem a2_cell (k : ℕ) (hk : k + 1 ≤ 655000) (δ : ℝ) (h0 : (k / 1000 : ℝ) ≤ δ)
    (h1 : δ ≤ (k / 1000 : ℝ) + 1 / 1000) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by
  set F : ℝ → ℂ := fun t => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t with hF
  have hi := interp_A4 F (48 * π ^ 2) (k / 1000) ((k / 1000 : ℝ) + 1 / 1000)
    (by linarith) a2_contDiff (fun v _ => a2_second_deriv v) δ ⟨h0, h1⟩
  have ga := a2_grid_certificate k (by omega)
  have gb := a2_grid_certificate (k + 1) hk
  have hcast : (((k + 1 : ℕ) : ℝ) / 1000) = (k / 1000 : ℝ) + 1 / 1000 := by
    push_cast; ring
  rw [hcast] at gb
  have hmax : max ‖F (k / 1000)‖ ‖F ((k / 1000 : ℝ) + 1 / 1000)‖ ≤ 31.520695 :=
    max_le ga gb
  have hp : π ^ 2 < 10 := by nlinarith [pi_lt_d2, pi_pos]
  have herr : ((k / 1000 : ℝ) + 1 / 1000 - k / 1000) ^ 2 / 8 * (48 * π ^ 2) ≤ 0.000237 := by
    ring_nf
    nlinarith
  change ‖F δ‖ ≤ 31.521
  linarith

/-- The parent `a2_compact` statement from the leaves, with the low branch handled by the parent. -/
theorem a2_compact_mid (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 655) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by
  rcases eq_or_lt_of_le h1 with h | h
  · exact norm_second_fourier_eta2_le_of_large (by rw [h]; norm_num)
  · set k : ℕ := ⌊1000 * δ⌋₊ with hk
    have hfl : (k : ℝ) ≤ 1000 * δ := Nat.floor_le (by positivity)
    have hlt : 1000 * δ < k + 1 := Nat.lt_floor_add_one _
    have hk1 : k < 655000 := by
      have : (k : ℝ) < 655000 := by linarith
      exact_mod_cast this
    exact a2_cell k (by omega) δ (by rw [div_le_iff₀ (by norm_num)]; linarith)
      (by
        have : (k : ℝ) / 1000 + 1 / 1000 = (k + 1) / 1000 := by ring
        rw [this, le_div_iff₀ (by norm_num)]; linarith)

end LeanLab.HelfgottArcs.Decomp119bLeavesA2
