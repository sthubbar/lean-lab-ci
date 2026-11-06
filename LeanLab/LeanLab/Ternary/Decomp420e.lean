/-
Helfgott https://arxiv.org/abs/1312.7748v2, pages 10 and 69, equations 3.3 and 7.49.
Fourier inversion for absolutely summable coefficient sequences.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420a
import LeanLab.Ternary.MMSOrthogonality

namespace LeanLab.Ternary.Task420
open Finset MeasureTheory
open LeanLab.Ternary.MMS

/-- The exact infinite Fourier integrand used in section 7.4.
Helfgott page 69, equation 7.49, with x and the scale 49 from page 59.
The finite weighted count retains only triples summing to N. -/
noncomputable def helfgottIntegrand (N : ℕ) (α : ℝ) : ℂ :=
  let x := LeanLab.Helfgott2013.xOf N
  LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α x ^ 2 *
    LeanLab.HelfgottArcs.S
      (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
        LeanLab.HelfgottArcs.etaT2 (49 * t)) α x *
    LeanLab.HelfgottArcs.e (-(N : ℝ) * α)

/-- The natural index Fourier series with arbitrary complex coefficients.
Helfgott page 10 equation 3.1, with the coefficient sequence separated from its weight. -/
noncomputable def charSeries (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑' n : ℕ, a n * e ((n : ℝ) * α)

/-- Absolute coefficient summability makes the character series continuous.
Derived analytic justification for Helfgott page 10 equation 3.3. -/
theorem continuous_charSeries (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) :
    Continuous (charSeries a) := by
  exact continuous_tsum (fun n => by unfold e; fun_prop) ha
    (fun n α => by simp only [norm_mul, norm_e, mul_one, le_refl])

/-- Integrating an absolutely summable character series keeps exactly its zero frequencies.
Helfgott page 10 equation 3.3 and page 69 equation 7.49, the orthogonality step. -/
theorem integral_l1_characters {ι : Type*} [Countable ι] (a : ι → ℂ) (k : ι → ℤ)
    (ha : Summable fun i => ‖a i‖) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ∑' i, a i * e ((k i : ℝ) * α)) =
      ∑' i, if k i = 0 then a i else 0 := by
  have hc (i : ι) : Continuous (fun α : ℝ => a i * e ((k i : ℝ) * α)) := by
    unfold e
    fun_prop
  have hi (i : ι) : IntegrableOn (fun α : ℝ => a i * e ((k i : ℝ) * α))
      (Set.Ioc (0 : ℝ) 1) := (hc i).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hn (i : ι) : (∫ α in Set.Ioc (0 : ℝ) 1, ‖a i * e ((k i : ℝ) * α)‖) = ‖a i‖ := by
    simp only [norm_mul, norm_e, mul_one]
    simp
  have hsum : Summable fun i => ∫ α in Set.Ioc (0 : ℝ) 1,
      ‖a i * e ((k i : ℝ) * α)‖ := by simpa only [hn] using ha
  have he (i : ι) : (∫ α in Set.Ioc (0 : ℝ) 1, a i * e ((k i : ℝ) * α)) =
      if k i = 0 then a i else 0 := by
    rw [MeasureTheory.integral_const_mul,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_e_int]
    split_ifs <;> simp
  have h := integral_tsum_of_summable_integral_norm hi hsum
  simpa only [he] using h.symm

/-- Absolute summability permits the three series to be expanded over all triples.
Helfgott page 10 equation 3.3 and page 69 equation 7.49. -/
theorem charSeries_triple_expansion (a b c : ℕ → ℂ)
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (hc : Summable fun n => ‖c n‖) (N : ℕ) (α : ℝ) :
    charSeries a α * charSeries b α * charSeries c α * e (-(N : ℝ) * α) =
      ∑' i : (ℕ × ℕ) × ℕ, (a i.1.1 * b i.1.2 * c i.2) *
        e ((((i.1.1 : ℤ) + i.1.2 + i.2 - N : ℤ) : ℝ) * α) := by
  have ha' : Summable fun n => ‖a n * e ((n : ℝ) * α)‖ := by
    simpa only [norm_mul, norm_e, mul_one] using ha
  have hb' : Summable fun n => ‖b n * e ((n : ℝ) * α)‖ := by
    simpa only [norm_mul, norm_e, mul_one] using hb
  have hc' : Summable fun n => ‖c n * e ((n : ℝ) * α)‖ := by
    simpa only [norm_mul, norm_e, mul_one] using hc
  unfold charSeries
  rw [tsum_mul_tsum_of_summable_norm ha' hb',
    tsum_mul_tsum_of_summable_norm (ha'.mul_norm hb') hc', ← tsum_mul_right]
  apply tsum_congr
  intro i
  have he : e ((i.1.1 : ℝ) * α) * e ((i.1.2 : ℝ) * α) * e ((i.2 : ℝ) * α) *
      e (-(N : ℝ) * α) = e ((((i.1.1 : ℤ) + i.1.2 + i.2 - N : ℤ) : ℝ) * α) := by
    rw [← e_add, ← e_add, ← e_add]
    congr 1
    push_cast
    ring
  calc
    _ = (a i.1.1 * b i.1.2 * c i.2) *
        (e ((i.1.1 : ℝ) * α) * e ((i.1.2 : ℝ) * α) * e ((i.2 : ℝ) * α) *
          e (-(N : ℝ) * α)) := by ring
    _ = _ := by rw [he]

/-- The circle integral of three absolutely summable series is their finite triple coefficient.
Helfgott page 10 equation 3.3 and page 69 equation 7.49.
Only nonnegative indices occur, so every retained coordinate is at most N. -/
theorem l1_triple_circle_identity (a b c : ℕ → ℂ)
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (hc : Summable fun n => ‖c n‖) (N : ℕ) :
    IntegrableOn (fun α : ℝ => charSeries a α * charSeries b α * charSeries c α *
      e (-(N : ℝ) * α)) (Set.Ioc (0 : ℝ) 1) ∧
      (∫ α in Set.Ioc (0 : ℝ) 1,
        charSeries a α * charSeries b α * charSeries c α * e (-(N : ℝ) * α)) =
          ∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1), ∑ r ∈ range (N + 1),
            if p + q + r = N then a p * b q * c r else 0 := by
  have hcont : Continuous (fun α : ℝ => charSeries a α * charSeries b α * charSeries c α *
      e (-(N : ℝ) * α)) := by
    apply ((continuous_charSeries a ha).mul (continuous_charSeries b hb)).mul
      (continuous_charSeries c hc) |>.mul
    unfold e
    fun_prop
  refine ⟨hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self, ?_⟩
  simp_rw [charSeries_triple_expansion a b c ha hb hc N]
  rw [integral_l1_characters _ _ ((ha.mul_norm hb).mul_norm hc)]
  let s : Finset ((ℕ × ℕ) × ℕ) :=
    (range (N + 1) ×ˢ range (N + 1)) ×ˢ range (N + 1)
  rw [tsum_eq_sum (s := s)]
  · dsimp [s]
    simp only [sum_product]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    have he : (p : ℤ) + q + r - N = 0 ↔ p + q + r = N := by omega
    simp only [he]
  · intro i hi
    have he : (i.1.1 : ℤ) + i.1.2 + i.2 - N ≠ 0 := by
      intro he
      apply hi
      simp only [s, mem_product, mem_range]
      omega
    simp only [he, ite_false]

/-- The paper exponential sum is the generic character series of its weighted coefficients.
Helfgott page 10 equation 3.1. This equality needs no convergence hypothesis. -/
theorem S_eq_charSeries (η : ℝ → ℝ) (x α : ℝ) :
    LeanLab.HelfgottArcs.S η α x =
      charSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (η (n / x) : ℂ)) α := by
  unfold LeanLab.HelfgottArcs.S charSeries
  apply tsum_congr
  intro n
  have he : LeanLab.HelfgottArcs.e (α * n) = e ((n : ℝ) * α) := by
    unfold LeanLab.HelfgottArcs.e e
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The sine bound gives a uniform coarse bound for the band limited kernel.
Helfgott page 56 smoothing definitions and major arcs appendix B.35 to B.38. -/
theorem FH_coarse_bound (u : ℝ) : |LeanLab.HelfgottArcs.FH 200 u| ≤ 200 / Real.pi := by
  unfold LeanLab.HelfgottArcs.FH
  by_cases hz : Real.log u = 0
  · simp [hz]; positivity
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
  apply (div_le_iff₀ (mul_pos Real.pi_pos (abs_pos.mpr hz))).mpr
  have h := Real.abs_sin_le_abs (x := 200 * Real.log u)
  rw [abs_mul] at h
  norm_num at h
  calc
    _ ≤ 200 * |Real.log u| := h
    _ = _ := by field_simp

/-- The compact polynomial factor divided by its argument has a uniform bound.
Helfgott page 56 smoothing definitions and major arcs appendix B.35 to B.38. -/
theorem hfun_div_bound {y : ℝ} (hy : 0 < y) :
    |LeanLab.HelfgottArcs.hfun y / y| ≤ 16 * Real.exp (3 / 2) := by
  unfold LeanLab.HelfgottArcs.hfun
  split_ifs with h
  · have hy2 : 0 ≤ 2 - y := by linarith [h.2]
    have hpoly : 0 ≤ y * (2 - y) ^ 3 := by positivity
    have hp : y * (2 - y) ^ 3 ≤ 16 := by
      have hc : (2 - y) ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      nlinarith
    have he : Real.exp (y - 1 / 2) ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr (by linarith)
    have hid : y ^ 2 * (2 - y) ^ 3 * Real.exp (y - 1 / 2) / y =
        y * (2 - y) ^ 3 * Real.exp (y - 1 / 2) := by field_simp
    rw [hid, abs_of_nonneg (mul_nonneg hpoly (Real.exp_pos _).le)]
    exact mul_le_mul hp he (Real.exp_pos _).le (by norm_num)
  · simp only [zero_div, abs_zero]; positivity

/-- The compact support and bounded kernel give a coarse convolution bound.
Helfgott page 56 smoothing definitions and major arcs appendix B.35 to B.38. -/
theorem mconv_hfun_coarse_bound (t : ℝ) :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
      (LeanLab.HelfgottArcs.FH 200) t| ≤
      32 * Real.exp (3 / 2) * (200 / Real.pi) := by
  let C : ℝ := 16 * Real.exp (3 / 2) * (200 / Real.pi)
  unfold LeanLab.HelfgottArcs.mconv
  have hr : (∫ y in Set.Ioi (0 : ℝ), LeanLab.HelfgottArcs.hfun y *
      LeanLab.HelfgottArcs.FH 200 (t / y) / y) =
      ∫ y in Set.Ioc (0 : ℝ) 2, LeanLab.HelfgottArcs.hfun y *
        LeanLab.HelfgottArcs.FH 200 (t / y) / y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun y hy => hy.1)
    intro y hy
    have hy2 : ¬ y ≤ 2 := by intro h; exact hy.2 ⟨hy.1, h⟩
    simp [LeanLab.HelfgottArcs.hfun, hy2]
  rw [hr]
  calc
    _ ≤ ∫ y in Set.Ioc (0 : ℝ) 2, |LeanLab.HelfgottArcs.hfun y *
        LeanLab.HelfgottArcs.FH 200 (t / y) / y| := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioc (0 : ℝ) 2))
        (fun y => LeanLab.HelfgottArcs.hfun y * LeanLab.HelfgottArcs.FH 200 (t / y) / y))
    _ ≤ ∫ _y in Set.Ioc (0 : ℝ) 2, C := by
      apply setIntegral_mono_of_nonneg (fun y hy => abs_nonneg _) ?_
        (integrableOn_const (by simp))
      intro y hy
      have hid : LeanLab.HelfgottArcs.hfun y * LeanLab.HelfgottArcs.FH 200 (t / y) / y =
          (LeanLab.HelfgottArcs.hfun y / y) * LeanLab.HelfgottArcs.FH 200 (t / y) := by ring
      rw [hid, abs_mul]
      exact mul_le_mul (hfun_div_bound hy.1) (FH_coarse_bound _) (abs_nonneg _) (by positivity)
    _ = _ := by simp [C]; ring

/-- The actual eta plus has a polynomial times Gaussian majorant.
Helfgott page 56 smoothing definitions and major arcs appendix B.35 to B.38. -/
theorem etaPlus_gaussian_bound {t : ℝ} (ht : 0 ≤ t) :
    |LeanLab.HelfgottArcs.etaPlus t| ≤
      (32 * Real.exp (3 / 2) * (200 / Real.pi)) * t * Real.exp (-t ^ 2 / 2) := by
  unfold LeanLab.HelfgottArcs.etaPlus
  split_ifs with h
  · rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mconv_hfun_coarse_bound t) ht) (Real.exp_pos _).le
  · simp only [abs_zero]; positivity

/-- LEAF. The actual eta plus von Mangoldt coefficients are absolutely summable.
Helfgott page 10 equation 3.1 and the eta plus construction on page 24.
The cited major arcs paper 1305.2897v4 pages 76 and 77, equations B.35 to B.38,
controls the band limited factor; the remaining Gaussian factor gives decay.
This leaf has no Fourier integral or prime representation conclusion. -/
theorem etaPlus_coefficients_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ := by
  let s : ℝ := 1 / x
  let K : ℝ := (32 * Real.exp (3 / 2) * (200 / Real.pi)) * s
  have hs : 0 < s := by dsimp [s]; positivity
  have ht : 0 < s ^ 2 / (2 * Real.pi) := by positivity
  have hsum := (HurwitzKernelBounds.summable_f_nat 2 0 ht).mul_left K
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hsum
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ n :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn)
  have hplus := etaPlus_gaussian_bound (show 0 ≤ s * n by positivity)
  have he : (n : ℝ) / x = s * n := by dsimp [s]; ring
  rw [he]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
  calc
    _ ≤ (n : ℝ) * ((32 * Real.exp (3 / 2) * (200 / Real.pi)) * (s * n) *
        Real.exp (-(s * n) ^ 2 / 2)) := mul_le_mul hΛ hplus (abs_nonneg _) hn
    _ = K * HurwitzKernelBounds.f_nat 2 0 (s ^ 2 / (2 * Real.pi)) n := by
      have hex : -(s * (n : ℝ)) ^ 2 / 2 =
          -Real.pi * (n : ℝ) ^ 2 * (s ^ 2 / (2 * Real.pi)) := by field_simp
      dsimp [K, HurwitzKernelBounds.f_nat]
      simp only [add_zero]
      rw [hex]
      ring

/-- Gaussian dilation bound on the compact Mellin support.
Helfgott page 25 equation 4.7. -/
theorem phi_scale_gaussian_bound {w t : ℝ} (hw : 0 ≤ w)
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    LeanLab.Helfgott2013.GaussianL2.phi (w / t) ≤
      16 * w ^ 2 * Real.exp (-w ^ 2 / 2) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hlow : w ≤ w / t := (le_div_iff₀ ht0).mpr (by nlinarith [ht.2])
  have hhigh : w / t ≤ 4 * w := (div_le_iff₀ ht0).mpr (by nlinarith [ht.1])
  have hz : 0 ≤ w / t := div_nonneg hw ht0.le
  have hsqlo : w ^ 2 ≤ (w / t) ^ 2 := by nlinarith
  have hsqhi : (w / t) ^ 2 ≤ 16 * w ^ 2 := by nlinarith
  have he := Real.exp_le_exp.mpr (show -(w / t) ^ 2 / 2 ≤ -w ^ 2 / 2 by linarith)
  unfold LeanLab.Helfgott2013.GaussianL2.phi
  exact mul_le_mul hsqhi he (Real.exp_pos _).le (by positivity)

/-- A coarse Gaussian bound for the exact compact Mellin convolution.
Helfgott page 25 equation 4.7 and page 60 equation 7.19. -/
theorem etaStar_gaussian_bound {w : ℝ} (hw : 0 ≤ w) :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2 w| ≤
      64 * Real.log 2 ^ 2 * w ^ 2 * Real.exp (-w ^ 2 / 2) := by
  rw [etaStar_eq_mellin hw,
    abs_of_nonneg (LeanLab.Helfgott2013.MellinSup.mellin_sup w).1]
  have he (t : ℝ) : 0 ≤ LeanLab.Helfgott2013.EtaTwo.etaTwo t := by
    unfold LeanLab.Helfgott2013.EtaTwo.etaTwo
    split_ifs <;> positivity
  have htne : ∀ t ∈ Set.Icc (1 / 4 : ℝ) 1, t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hp : Continuous LeanLab.Helfgott2013.GaussianL2.phi := by
    unfold LeanLab.Helfgott2013.GaussianL2.phi
    fun_prop
  have hc : ContinuousOn (fun t : ℝ => LeanLab.Helfgott2013.EtaTwo.etaTwo t *
      LeanLab.Helfgott2013.GaussianL2.phi (w / t) / t) (Set.Icc (1 / 4 : ℝ) 1) :=
    (LeanLab.Helfgott2013.EtaTwo.continuousOn_etaTwo.mul (hp.comp_continuousOn
      (continuousOn_const.div continuousOn_id htne))).div continuousOn_id htne
  have hg : ContinuousOn (fun t : ℝ => LeanLab.Helfgott2013.EtaTwo.etaTwo t / t *
      (16 * w ^ 2 * Real.exp (-w ^ 2 / 2))) (Set.Icc (1 / 4 : ℝ) 1) :=
    (LeanLab.Helfgott2013.EtaTwo.continuousOn_etaTwo.div continuousOn_id htne).mul_const _
  calc
    _ ≤ ∫ t in (1 / 4 : ℝ)..1, LeanLab.Helfgott2013.EtaTwo.etaTwo t / t *
        (16 * w ^ 2 * Real.exp (-w ^ 2 / 2)) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable_of_Icc (by norm_num))
        (hg.intervalIntegrable_of_Icc (by norm_num))
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      convert mul_le_mul_of_nonneg_left (phi_scale_gaussian_bound hw ht)
        (div_nonneg (he t) ht0.le) using 1 <;> ring
    _ = _ := by
      rw [intervalIntegral.integral_mul_const,
        LeanLab.Helfgott2013.EtaTwoMoments.etaTwo_div_moment_compact]
      ring

/-- LEAF. The actual eta star von Mangoldt coefficients are absolutely summable.
Helfgott page 25 equation 4.7 and page 60 equation 7.19.
Eta two has compact support in one quarter to one, and the other Mellin factor
is a Gaussian times its squared argument. The scale is fixed at 49 as on page 59.
This leaf has no major or minor arc bound. -/
theorem etaStar_coefficients_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
          (49 * (n / x)) : ℂ)‖ := by
  let s : ℝ := 49 / x
  let K : ℝ := 64 * Real.log 2 ^ 2 * s ^ 2
  have hs : 0 < s := by dsimp [s]; positivity
  have ht : 0 < s ^ 2 / (2 * Real.pi) := by positivity
  have hsum := (HurwitzKernelBounds.summable_f_nat 3 0 ht).mul_left K
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hsum
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ n :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn)
  have hstar := etaStar_gaussian_bound (show 0 ≤ s * n by positivity)
  have he : 49 * ((n : ℝ) / x) = s * n := by dsimp [s]; ring
  rw [he]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
  calc
    _ ≤ (n : ℝ) * (64 * Real.log 2 ^ 2 * (s * n) ^ 2 * Real.exp (-(s * n) ^ 2 / 2)) :=
      mul_le_mul hΛ hstar (abs_nonneg _) hn
    _ = K * HurwitzKernelBounds.f_nat 3 0 (s ^ 2 / (2 * Real.pi)) n := by
      have hex : -(s * (n : ℝ)) ^ 2 / 2 =
          -Real.pi * (n : ℝ) ^ 2 * (s ^ 2 / (2 * Real.pi)) := by
        field_simp
      dsimp [K, HurwitzKernelBounds.f_nat]
      simp only [add_zero]
      rw [hex]
      ring

/-- The exact existing Fourier identity follows from two one dimensional convergence inputs.
Helfgott page 69 equation 7.49, with its weights and scale unchanged.
Both convergence inputs are proved below the compact support and Gaussian estimates. -/
theorem helfgott_fourier_identity_decomposed (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    IntegrableOn (helfgottIntegrand N) (Set.Ioc (0 : ℝ) 1) ∧
      (Task379.weightedTotal N (Task379.helfgottTripleWeight N) : ℂ) =
        ∫ α in Set.Ioc (0 : ℝ) 1, helfgottIntegrand N α := by
  let x := LeanLab.Helfgott2013.xOf N
  have hx : 0 < x := by
    have hn : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by norm_num at hN; omega)
    dsimp [x, LeanLab.Helfgott2013.xOf, LeanLab.Helfgott2013.ratio]
    positivity
  let a := fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)
  let c := fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    (LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
      (49 * (n / x)) : ℂ)
  have h := l1_triple_circle_identity a a c
    (etaPlus_coefficients_summable hx) (etaPlus_coefficients_summable hx)
    (etaStar_coefficients_summable hx) N
  have he : (fun α : ℝ => charSeries a α * charSeries a α * charSeries c α *
      e (-(N : ℝ) * α)) = helfgottIntegrand N := by
    funext α
    unfold helfgottIntegrand
    simp only [S_eq_charSeries, pow_two]
    rfl
  rw [he] at h
  have ht : (∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1), ∑ r ∈ range (N + 1),
      if p + q + r = N then a p * a q * c r else 0) =
      (Task379.weightedTotal N (Task379.helfgottTripleWeight N) : ℂ) := by
    unfold Task379.weightedTotal
    simp only [Complex.ofReal_sum]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    split_ifs
    · dsimp [a, c, x, Task379.helfgottTripleWeight]
      push_cast
      ring
    · norm_num
  rw [ht] at h
  exact ⟨h.1, h.2.symm⟩

end LeanLab.Ternary.Task420
