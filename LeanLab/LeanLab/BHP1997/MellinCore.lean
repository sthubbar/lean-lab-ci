/-
Route burst burst-20261124, session S4, unit S4-28, BHP1997. The proof of
`S64LowExcCharNP.leaf_mellin_mean_value`, P0069 Baker Harman Pintz 1997, page 44, proof of
Lemma 29, "By a variant of [8], Lemma 2", collected in one file below
S64LowExcCharNonprincipal.lean so that file can import it and lose its sorry.

The pieces are those of the burst chain SPLIT_leaf_mellin_mean_value,
SPLIT_leaf_gallagher_mean_value, SPLIT_leaf_plancherel_log_window,
SPLIT_leaf_gaussian_weighted_mean_value and SPLIT_leaf_gaussian_expansion, in bottom up order,
in the namespace `MellinCore`, each leaf proved by the assembly of the file below it:
Gaussian majorant `exp(-u^2/4)` of the window, expansion of the square with Fubini, the
Gaussian Fourier transform from Mathlib `integral_cexp_quadratic`, the kernel bound with
constant `2π`, the substitution `y = Y e^u`, and `y^(1/2+it) = y^(1/2) y^(it)`.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.Prep1121LowExcLemma29

namespace LeanLab.BHP1997.MellinCore
open Complex MeasureTheory

/-- Standard analysis: conjugation commutes with the interval integral. -/
theorem interval_conj_aux {a b : ℝ} (f : ℝ → ℂ) (hab : a ≤ b) :
    (starRingEnd ℂ) (∫ t in a..b, f t) = ∫ t in a..b, (starRingEnd ℂ) (f t) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, integral_conj]

/-- Standard analysis, Fubini on the line times an interval for a continuous function
dominated by a Gaussian in the first variable. -/
theorem swap_gaussian_interval {f : ℝ → ℝ → ℂ} (hf : Continuous (Function.uncurry f))
    {a b : ℝ} (hab : a ≤ b) (C : ℝ)
    (hb : ∀ u t, ‖f u t‖ ≤ C * Real.exp (-(1 / 4) * u ^ 2)) :
    ∫ u : ℝ, ∫ t in a..b, f u t = ∫ t in a..b, ∫ u : ℝ, f u t := by
  simp only [intervalIntegral.integral_of_le hab]
  apply integral_integral_swap
  refine Integrable.mono' ?_ hf.aestronglyMeasurable (ae_of_all _ fun p => hb p.1 p.2)
  have h1 := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul C
  exact h1.comp_fst (volume.restrict (Set.Ioc a b))

/-- Page 44, Gallagher's expansion and Fubini, for a continuous function bounded on the
whole line. -/
theorem gaussian_fubini_core (T : ℝ) (hTT : -T ≤ T) (g : ℝ → ℂ) (hg : Continuous g)
    (M : ℝ) (hgM : ∀ t, ‖g t‖ ≤ M) :
    (((∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
        ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T, g t * (starRingEnd ℂ) (g s) *
        ∫ u : ℝ, ((Real.exp (-(1 / 4) * u ^ 2) : ℝ) : ℂ) *
          cexp ((u : ℂ) * (((t - s : ℝ) : ℂ) * I)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  have hE : ∀ u t s : ℝ, cexp ((u : ℂ) * ((t : ℂ) * I)) *
      (starRingEnd ℂ) (cexp ((u : ℂ) * ((s : ℂ) * I))) =
      cexp ((u : ℂ) * (((t - s : ℝ) : ℂ) * I)) := by
    intro u t s
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hnE : ∀ u x : ℝ, ‖cexp ((u : ℂ) * ((x : ℂ) * I))‖ = 1 := by
    intro u x
    rw [show (u : ℂ) * ((x : ℂ) * I) = ((u * x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  let G : ℝ → ℝ → ℝ → ℂ := fun u t s =>
    ((Real.exp (-(1 / 4) * u ^ 2) : ℝ) : ℂ) *
      (g t * (starRingEnd ℂ) (g s) * cexp ((u : ℂ) * (((t - s : ℝ) : ℂ) * I)))
  have hGc : Continuous fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 := by
    refine (Complex.continuous_ofReal.comp (by fun_prop)).mul
      (((hg.comp (continuous_fst.comp continuous_snd)).mul
        (Complex.continuous_conj.comp (hg.comp (continuous_snd.comp continuous_snd)))).mul
        (Continuous.cexp (by fun_prop)))
  have hGb : ∀ u t s, ‖G u t s‖ ≤ M ^ 2 * Real.exp (-(1 / 4) * u ^ 2) := by
    intro u t s
    simp only [G]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), hnE, mul_one]
    have := mul_le_mul (hgM t) (hgM s) (norm_nonneg _) hM0
    nlinarith [Real.exp_pos (-(1 / 4) * u ^ 2)]
  have hpt : ∀ u : ℝ, ((Real.exp (-(1 / 4) * u ^ 2) *
      ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 : ℝ) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T, G u t s := by
    intro u
    rw [Complex.ofReal_mul, h1, interval_conj_aux _ hTT,
      ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    beta_reduce
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    beta_reduce
    simp only [G, map_mul]
    rw [← hE u t s]
    ring
  have hfun : (fun u : ℝ => (((Real.exp (-(1 / 4) * u ^ 2) *
      ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 : ℝ)) : ℂ)) =
      fun u => ∫ t in (-T)..T, ∫ s in (-T)..T, G u t s := funext hpt
  rw [← integral_complex_ofReal, hfun]
  -- first swap, u and t
  have hF1 : Continuous (Function.uncurry fun u t => ∫ s in (-T)..T, G u t s) := by
    have : Continuous (Function.uncurry fun (p : ℝ × ℝ) s => G p.1 p.2 s) :=
      hGc.comp (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this _ _
  have hF1b : ∀ u t, ‖∫ s in (-T)..T, G u t s‖ ≤
      (M ^ 2 * |T - -T|) * Real.exp (-(1 / 4) * u ^ 2) := by
    intro u t
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T) (f := fun s => G u t s) (fun s _ => hGb u t s)
    linarith
  rw [swap_gaussian_interval hF1 hTT _ hF1b]
  apply intervalIntegral.integral_congr
  intro t _
  beta_reduce
  have hF2 : Continuous (Function.uncurry fun u s => G u t s) :=
    hGc.comp (by fun_prop : Continuous fun q : ℝ × ℝ => (q.1, t, q.2))
  rw [swap_gaussian_interval hF2 hTT _ (fun u s => hGb u t s)]
  apply intervalIntegral.integral_congr
  intro s _
  beta_reduce
  rw [← integral_const_mul]
  congr 1
  funext u
  simp only [G]
  ring

/-- PROVED, formerly a LEAF of class MEDIUM: page 44, proof of Lemma 29, the variant of
[8] Lemma 2, expansion of the square and Fubini. P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2",
Gallagher's first step: with `F(u) = ∫_{-T}^{T} h(t) e^(itu) dt`,
`|F(u)|^2 = ∫∫ h(t) conj h(s) e^(iu(t-s)) dt ds`, and the integral over `u ∈ ℝ` against
`w(u) = exp(-u^2/4)` moves inside the double integral, the integrand being bounded by
`w(u) |h(t)| |h(s)|`, integrable on `ℝ × [-T, T]^2`. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gaussian_fubini (T : ℝ) (hT : 0 ≤ T) (h : ℝ → ℂ) (hh : Continuous h) :
    (((∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
        ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T, h t * (starRingEnd ℂ) (h s) *
        ∫ u : ℝ, ((Real.exp (-(1 / 4) * u ^ 2) : ℝ) : ℂ) *
          cexp ((u : ℂ) * (((t - s : ℝ) : ℂ) * I)) := by
  have hTT : -T ≤ T := by linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hh.continuousOn (s := Set.Icc (-T) T))
  let c : ℝ → ℝ := fun t => max (-T) (min t T)
  have hc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcmem : ∀ t, c t ∈ Set.Icc (-T) T :=
    fun t => ⟨le_max_left _ _, max_le hTT (min_le_right _ _)⟩
  have hceq : ∀ t ∈ Set.uIcc (-T) T, c t = t := by
    intro t ht
    rw [Set.uIcc_of_le hTT] at ht
    show max (-T) (min t T) = t
    rw [min_eq_left ht.2, max_eq_right ht.1]
  let g : ℝ → ℂ := fun t => h (c t)
  have hgeq : ∀ t ∈ Set.uIcc (-T) T, g t = h t := by
    intro t ht
    show h (c t) = h t
    rw [hceq t ht]
  have core := gaussian_fubini_core T hTT g (hh.comp hc) M (fun t => hM _ (hcmem t))
  have hL : ∀ u : ℝ, ∫ t in (-T)..T, g t * cexp ((u : ℂ) * ((t : ℂ) * I)) =
      ∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I)) := by
    intro u
    apply intervalIntegral.integral_congr
    intro t ht
    beta_reduce
    rw [hgeq t ht]
  simp only [hL] at core
  rw [core]
  apply intervalIntegral.integral_congr
  intro t ht
  beta_reduce
  apply intervalIntegral.integral_congr
  intro s hs
  beta_reduce
  rw [hgeq t ht, hgeq s hs]

/-- Standard analysis, the Fourier transform of the Gaussian weight of page 44:
`∫_ℝ exp(-u^2/4) e^(iux) du = 2 √π exp(-x^2)`, from Mathlib `integral_cexp_quadratic`. -/
theorem gaussian_fourier (x : ℝ) :
    ∫ u : ℝ, ((Real.exp (-(1 / 4) * u ^ 2) : ℝ) : ℂ) * cexp ((u : ℂ) * ((x : ℂ) * I)) =
      ((2 * Real.sqrt Real.pi * Real.exp (-x ^ 2) : ℝ) : ℂ) := by
  have hq := integral_cexp_quadratic (b := -(1 / 4 : ℂ)) (by norm_num) ((x : ℂ) * I) 0
  have hfun : (fun u : ℝ => ((Real.exp (-(1 / 4) * u ^ 2) : ℝ) : ℂ) *
      cexp ((u : ℂ) * ((x : ℂ) * I))) =
      fun u : ℝ => cexp (-(1 / 4 : ℂ) * (u : ℂ) ^ 2 + (x : ℂ) * I * u + 0) := by
    funext u
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun, hq]
  have h1 : (Real.pi : ℂ) / -(-(1 / 4 : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (0 : ℂ) - ((x : ℂ) * I) ^ 2 / (4 * -(1 / 4 : ℂ)) = ((-x ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]
    push_cast
    ring
  have h3 : ((4 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((2 * Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h1, h2, h3, ← Complex.ofReal_exp]
  push_cast
  ring

/-- PROVED from the leaves of SPLIT_leaf_gaussian_expansion.lean, formerly a LEAF of class
MEDIUM: page 44, proof of Lemma 29, the variant of [8] Lemma 2, expansion of the square.
P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2", Gallagher's first step: with `w(u) = exp(-u^2/4)` and `F(u) = ∫_{-T}^{T} h(t) e^(itu) dt`,
`∫_ℝ w(u) |F(u)|^2 du = ∫∫ h(t) conj h(s) ŵ(t - s) dt ds` with
`ŵ(x) = ∫_ℝ w(u) e^(ixu) du = 2 √π exp(-x^2)`, by Fubini and the Gaussian integral.
CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gaussian_expansion (T : ℝ) (hT : 0 ≤ T) (h : ℝ → ℂ) (hh : Continuous h) :
    (((∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
        ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T,
        h t * (starRingEnd ℂ) (h s) *
          (((2 * Real.sqrt Real.pi * Real.exp (-(t - s) ^ 2) : ℝ)) : ℂ) := by
  rw [leaf_gaussian_fubini T hT h hh]
  apply intervalIntegral.integral_congr
  intro t _
  apply intervalIntegral.integral_congr
  intro s _
  beta_reduce
  rw [gaussian_fourier (t - s)]

/-- Standard analysis, Fubini for a continuous function on a box. -/
theorem interval_integral_swap_of_continuous {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply MeasureTheory.integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- Standard analysis. The Gaussian kernel `2 √π exp(-(t-s)^2)` integrates over any
interval in `s` to at most `2π`. -/
theorem gaussian_kernel_interval_le (t T : ℝ) (hT : 0 ≤ T) :
    ∫ s in (-T)..T, 2 * Real.sqrt Real.pi * Real.exp (-(t - s) ^ 2) ≤ 2 * Real.pi := by
  have h1 := intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => 2 * Real.sqrt Real.pi * Real.exp (-x ^ 2)) t (a := -T) (b := T)
  rw [h1]
  have hint : Integrable (fun x : ℝ => 2 * Real.sqrt Real.pi * Real.exp (-x ^ 2)) := by
    have := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (2 * Real.sqrt Real.pi)
    simpa using this
  have hle : t - T ≤ t - -T := by linarith
  rw [intervalIntegral.integral_of_le hle]
  refine (setIntegral_le_integral hint (ae_of_all _ (fun x => ?_))).trans (le_of_eq ?_)
  · show (0 : ℝ) ≤ 2 * Real.sqrt Real.pi * Real.exp (-x ^ 2)
    positivity
  · rw [integral_const_mul]
    have hg := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at hg
    rw [hg, mul_assoc, Real.mul_self_sqrt Real.pi_pos.le]

/-- PROVED, formerly a LEAF of class MEDIUM: page 44, proof of Lemma 29, the variant of [8]
Lemma 2, the kernel bound. P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2", Gallagher's
second step: the double integral against the positive kernel `2 √π exp(-(t-s)^2)` is at
most `2π ∫_{-T}^{T} |h|^2`, by `|h(t) h(s)| ≤ (|h(t)|^2 + |h(s)|^2)/2`, symmetry in `t, s`
and `∫_ℝ 2 √π exp(-x^2) dx = 2π`. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gaussian_kernel_schur (T : ℝ) (hT : 0 ≤ T) (h : ℝ → ℂ) (hh : Continuous h) :
    ‖∫ t in (-T)..T, ∫ s in (-T)..T,
        h t * (starRingEnd ℂ) (h s) *
          (((2 * Real.sqrt Real.pi * Real.exp (-(t - s) ^ 2) : ℝ)) : ℂ)‖ ≤
      2 * Real.pi * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
  have hTT : -T ≤ T := by linarith
  set k : ℝ → ℝ → ℝ := fun t s => 2 * Real.sqrt Real.pi * Real.exp (-(t - s) ^ 2) with hkdef
  have hk0 : ∀ t s, 0 ≤ k t s := fun t s => by simp only [hkdef]; positivity
  have hkc : Continuous (Function.uncurry k) := by
    simp only [hkdef]; fun_prop
  have hac : Continuous fun t => ‖h t‖ := hh.norm
  -- pointwise norm
  have hpt : ∀ t s, ‖h t * (starRingEnd ℂ) (h s) * ((k t s : ℝ) : ℂ)‖ =
      ‖h t‖ * ‖h s‖ * k t s := by
    intro t s
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hk0 t s)]
  -- step 1: the norm of the double integral
  have hP : Continuous (Function.uncurry fun t s => ‖h t‖ * ‖h s‖ * k t s) := by
    have : Continuous fun p : ℝ × ℝ => ‖h p.1‖ * ‖h p.2‖ * k p.1 p.2 :=
      ((hac.comp continuous_fst).mul (hac.comp continuous_snd)).mul hkc
    exact this
  have hPint : Continuous fun t => ∫ s in (-T)..T, ‖h t‖ * ‖h s‖ * k t s :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hP _ _
  have step1 : ‖∫ t in (-T)..T, ∫ s in (-T)..T,
        h t * (starRingEnd ℂ) (h s) * ((k t s : ℝ) : ℂ)‖ ≤
      ∫ t in (-T)..T, ∫ s in (-T)..T, ‖h t‖ * ‖h s‖ * k t s := by
    refine intervalIntegral.norm_integral_le_of_norm_le hTT (ae_of_all _ (fun t _ => ?_))
      (hPint.intervalIntegrable _ _)
    refine intervalIntegral.norm_integral_le_of_norm_le hTT (ae_of_all _ (fun s _ => ?_))
      ((hP.comp (Continuous.prodMk_right t)).intervalIntegrable _ _)
    exact (hpt t s).le
  -- step 2: AM GM
  have hQ1 : Continuous (Function.uncurry fun t s => ‖h t‖ ^ 2 * k t s) := by
    have : Continuous fun p : ℝ × ℝ => ‖h p.1‖ ^ 2 * k p.1 p.2 :=
      ((hac.comp continuous_fst).pow 2).mul hkc
    exact this
  have hQ2 : Continuous (Function.uncurry fun t s => ‖h s‖ ^ 2 * k t s) := by
    have : Continuous fun p : ℝ × ℝ => ‖h p.2‖ ^ 2 * k p.1 p.2 :=
      ((hac.comp continuous_snd).pow 2).mul hkc
    exact this
  have hQ1i : Continuous fun t => ∫ s in (-T)..T, ‖h t‖ ^ 2 * k t s :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hQ1 _ _
  have hQ2i : Continuous fun t => ∫ s in (-T)..T, ‖h s‖ ^ 2 * k t s :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hQ2 _ _
  have step2 : ∫ t in (-T)..T, ∫ s in (-T)..T, ‖h t‖ * ‖h s‖ * k t s ≤
      ∫ t in (-T)..T, ((∫ s in (-T)..T, ‖h t‖ ^ 2 * k t s) +
        ∫ s in (-T)..T, ‖h s‖ ^ 2 * k t s) / 2 := by
    apply intervalIntegral.integral_mono_on hTT (hPint.intervalIntegrable _ _)
      (((hQ1i.add hQ2i).div_const 2).intervalIntegrable _ _)
    intro t _
    have c1 : Continuous fun s => ‖h t‖ ^ 2 * k t s := hQ1.comp (Continuous.prodMk_right t)
    have c2 : Continuous fun s => ‖h s‖ ^ 2 * k t s := hQ2.comp (Continuous.prodMk_right t)
    show ∫ s in (-T)..T, ‖h t‖ * ‖h s‖ * k t s ≤
      ((∫ s in (-T)..T, ‖h t‖ ^ 2 * k t s) + ∫ s in (-T)..T, ‖h s‖ ^ 2 * k t s) / 2
    rw [← intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
      ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_mono_on hTT
      ((hP.comp (Continuous.prodMk_right t)).intervalIntegrable _ _)
    · exact ((c1.add c2).div_const 2).intervalIntegrable _ _
    · intro s _
      have := hk0 t s
      have hsq := sq_nonneg (‖h t‖ - ‖h s‖)
      show ‖h t‖ * ‖h s‖ * k t s ≤ (‖h t‖ ^ 2 * k t s + ‖h s‖ ^ 2 * k t s) / 2
      nlinarith [mul_nonneg hsq this]
  -- step 3: the two halves
  have hsplit : ∫ t in (-T)..T, ((∫ s in (-T)..T, ‖h t‖ ^ 2 * k t s) +
        ∫ s in (-T)..T, ‖h s‖ ^ 2 * k t s) / 2 =
      ((∫ t in (-T)..T, ∫ s in (-T)..T, ‖h t‖ ^ 2 * k t s) +
        ∫ t in (-T)..T, ∫ s in (-T)..T, ‖h s‖ ^ 2 * k t s) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (hQ1i.intervalIntegrable _ _) (hQ2i.intervalIntegrable _ _)]
  have half1 : ∫ t in (-T)..T, ∫ s in (-T)..T, ‖h t‖ ^ 2 * k t s ≤
      2 * Real.pi * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hTT (hQ1i.intervalIntegrable _ _)
      ((continuous_const.mul (hac.pow 2)).intervalIntegrable _ _)
    intro t _
    rw [intervalIntegral.integral_const_mul]
    have := gaussian_kernel_interval_le t T hT
    have h0 : 0 ≤ ‖h t‖ ^ 2 := sq_nonneg _
    calc ‖h t‖ ^ 2 * ∫ s in (-T)..T, k t s ≤ ‖h t‖ ^ 2 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_left this h0
      _ = 2 * Real.pi * ‖h t‖ ^ 2 := by ring
  have half2 : ∫ t in (-T)..T, ∫ s in (-T)..T, ‖h s‖ ^ 2 * k t s ≤
      2 * Real.pi * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
    rw [interval_integral_swap_of_continuous hQ2 hTT hTT, ← intervalIntegral.integral_const_mul]
    have hR : Continuous fun s => ∫ t in (-T)..T, ‖h s‖ ^ 2 * k t s := by
      have : Continuous (Function.uncurry fun s t => ‖h s‖ ^ 2 * k t s) := by
        have : Continuous fun p : ℝ × ℝ => ‖h p.1‖ ^ 2 * k p.2 p.1 :=
          ((hac.comp continuous_fst).pow 2).mul (hkc.comp continuous_swap)
        exact this
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this _ _
    apply intervalIntegral.integral_mono_on hTT (hR.intervalIntegrable _ _)
      ((continuous_const.mul (hac.pow 2)).intervalIntegrable _ _)
    intro s _
    rw [intervalIntegral.integral_const_mul]
    have hks : ∫ t in (-T)..T, k t s ≤ 2 * Real.pi := by
      have := gaussian_kernel_interval_le s T hT
      refine le_of_eq_of_le ?_ this
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hkdef]
      congr 2
      ring
    have h0 : 0 ≤ ‖h s‖ ^ 2 := sq_nonneg _
    calc ‖h s‖ ^ 2 * ∫ t in (-T)..T, k t s ≤ ‖h s‖ ^ 2 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_left hks h0
      _ = 2 * Real.pi * ‖h s‖ ^ 2 := by ring
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := hsplit
    _ ≤ (2 * Real.pi * (∫ t in (-T)..T, ‖h t‖ ^ 2) +
          2 * Real.pi * ∫ t in (-T)..T, ‖h t‖ ^ 2) / 2 := by linarith
    _ = 2 * Real.pi * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by ring

/-- PROVED here, the statement of the LEAF of the burst chain: page 44, proof of Lemma 29, the variant of [8] Lemma 2 with the Gaussian weight,
class HARD. P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2": with
`w(u) = exp(-u^2/4)`, `∫_ℝ w(u) |∫_{-T}^{T} h(t) e^(itu) dt|^2 du ≪ ∫_{-T}^{T} |h(t)|^2 dt`
for continuous `h`. Expanding the square and integrating in `u` first gives the kernel
`ŵ(t - s) = 2 √π exp(-(t-s)^2)`, and `|h(t) h(s)| ≤ (|h(t)|^2 + |h(s)|^2)/2` gives the
constant `2π`. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gaussian_weighted_mean_value :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ h : ℝ → ℂ, Continuous h →
      ∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
          ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 ≤
        K * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  intro T hT h hh
  have hA := leaf_gaussian_expansion T hT h hh
  have hB := leaf_gaussian_kernel_schur T hT h hh
  rw [← hA, Complex.norm_real, Real.norm_eq_abs] at hB
  exact (le_abs_self _).trans hB

/-- PROVED here, the statement of the LEAF of the burst chain: page 44, proof of Lemma 29, the Fourier side of the variant of [8] Lemma 2 after
the substitution `y = Y e^u`, class HARD. P0069 Baker Harman Pintz 1997, "By a variant of
[8], Lemma 2": on the fixed window `u ∈ [log(1/2), log 3]` of length `log 6`,
`∫ |∫_{-T}^{T} h(t) e^(itu) dt|^2 du ≪ ∫_{-T}^{T} |h(t)|^2 dt` with an absolute constant,
for continuous `h`. It holds by Plancherel, or by a smooth majorant of the window with a
nonnegative integrable Fourier transform. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_plancherel_log_window :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ h : ℝ → ℂ, Continuous h →
      ∫ u in (Real.log (1 / 2))..(Real.log 3),
          ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 ≤
        K * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := leaf_gaussian_weighted_mean_value
  refine ⟨3 * K, by positivity, ?_⟩
  intro T hT h hh
  have hlogle : Real.log (1 / 2) ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  set F : ℝ → ℂ := fun u => ∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I)) with hFdef
  have hFc : Continuous F := by
    have hu : Continuous fun p : ℝ × ℝ => h p.2 * cexp ((p.1 : ℂ) * ((p.2 : ℂ) * I)) :=
      (hh.comp continuous_snd).mul (Continuous.cexp (by fun_prop))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu _ _
  have hnorm1 : ∀ u t : ℝ, ‖h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ = ‖h t‖ := by
    intro u t
    rw [norm_mul, show (u : ℂ) * ((t : ℂ) * I) = ((u * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hFb : ∀ u, ‖F u‖ ≤ ∫ t in (-T)..T, ‖h t‖ := by
    intro u
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
    exact intervalIntegral.integral_congr (fun t _ => hnorm1 u t)
  set M : ℝ := ∫ t in (-T)..T, ‖h t‖ with hMdef
  have hwc : Continuous fun u : ℝ => Real.exp (-(1 / 4) * u ^ 2) := by fun_prop
  have hint : Integrable (fun u : ℝ => Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2) := by
    have hg := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (M ^ 2)
    refine hg.mono' (hwc.mul (hFc.norm.pow 2)).aestronglyMeasurable ?_
    refine ae_of_all _ (fun u => ?_)
    have hF0 : 0 ≤ ‖F u‖ := norm_nonneg _
    have hFM : ‖F u‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hF0 (hFb u) 2
    have hw0 : 0 < Real.exp (-(1 / 4) * u ^ 2) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2
        ≤ Real.exp (-(1 / 4) * u ^ 2) * M ^ 2 := mul_le_mul_of_nonneg_left hFM hw0.le
      _ = M ^ 2 * Real.exp (-(1 / 4) * u ^ 2) := by ring
  have hwin : ∫ u in (Real.log (1 / 2))..(Real.log 3), ‖F u‖ ^ 2 ≤
      ∫ u in (Real.log (1 / 2))..(Real.log 3),
        3 * (Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on hlogle
    · exact (hFc.norm.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul (hwc.mul (hFc.norm.pow 2))).intervalIntegrable _ _
    · intro u hu
      have hl2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
      have hlo : -1 ≤ u := by
        have := Real.log_two_lt_d9
        linarith [hu.1]
      have hup : u ≤ 2 := by
        have h3 : Real.log 3 ≤ 2 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          linarith [Real.add_one_le_exp (2 : ℝ)]
        linarith [hu.2]
      have hsq : u ^ 2 ≤ 4 := by nlinarith
      have hw : 1 / 3 ≤ Real.exp (-(1 / 4) * u ^ 2) := by
        have h1 : -1 ≤ -(1 / 4) * u ^ 2 := by nlinarith
        have h2 : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le (Real.exp_pos 1)
            (by linarith [Real.exp_one_lt_d9])
        exact h2.trans (Real.exp_le_exp.mpr h1)
      have hp := mul_le_mul_of_nonneg_right hw (sq_nonneg ‖F u‖)
      nlinarith
  rw [intervalIntegral.integral_const_mul] at hwin
  have hsub : ∫ u in (Real.log (1 / 2))..(Real.log 3),
        Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2 ≤
      ∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hlogle]
    refine setIntegral_le_integral hint (ae_of_all _ (fun u => ?_))
    show (0 : ℝ) ≤ Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2
    positivity
  have hK' := hK T hT h hh
  calc _ ≤ 3 * ∫ u in (Real.log (1 / 2))..(Real.log 3),
        Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2 := hwin
    _ ≤ 3 * ∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (by norm_num)
    _ ≤ 3 * (K * ∫ t in (-T)..T, ‖h t‖ ^ 2) := mul_le_mul_of_nonneg_left hK' (by norm_num)
    _ = 3 * K * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by ring

/-- Standard analysis. With the base kept at least `c > 0`, the parametric integral
`y ↦ ∫_a^b g(t) max(y, c)^(e(t)) dt` is continuous in `y`. -/
theorem continuous_max_cpow_integral {c : ℝ} (hc : 0 < c) {g : ℝ → ℂ} (hg : Continuous g)
    {e : ℝ → ℂ} (he : Continuous e) (a b : ℝ) :
    Continuous fun y : ℝ => ∫ t in a..b, g t * (((max y c : ℝ)) : ℂ) ^ e t := by
  have h : Continuous fun p : ℝ × ℝ => g p.2 * (((max p.1 c : ℝ)) : ℂ) ^ e p.2 := by
    refine (hg.comp continuous_snd).mul ?_
    refine Continuous.cpow ?_ (he.comp continuous_snd) ?_
    · exact Complex.continuous_ofReal.comp (continuous_fst.max continuous_const)
    · intro p
      exact Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le hc (le_max_right _ _))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h a b

/-- Standard complex analysis. For `Y > 0`, `(Y e^u)^(it) = Y^(it) e^(itu)`. -/
theorem ofReal_mul_exp_cpow {Y : ℝ} (hY : 0 < Y) (u t : ℝ) :
    (((Y * Real.exp u : ℝ)) : ℂ) ^ ((t : ℂ) * I) =
      (Y : ℂ) ^ ((t : ℂ) * I) * cexp ((u : ℂ) * ((t : ℂ) * I)) := by
  rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg hY.le (Real.exp_pos u).le]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]

/-- PROVED here, the statement of the LEAF of the burst chain: page 44, proof of Lemma 29, the variant of [8] Lemma 2 as printed, class HARD.
P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2,
`∫_{Y/2}^{3Y} |∫_T^{T'} g(t) y^(it) dt|^2 dy ≪ Y L ∫_T^{T'} |g(t)|^2 dt` whenever `g` is
continuous", on the symmetric range `[-T, T]` used on page 44 and in the form without the
factor `L`, which holds by Plancherel after `y = e^u` with an absolute constant, QUESTION 1
of the S64 note. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gallagher_mean_value :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y), ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 ≤
        K * Y * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := leaf_plancherel_log_window
  refine ⟨3 * K, by positivity, ?_⟩
  intro Y hY T hT g hg
  have hc : 0 < Y / 2 := by positivity
  have hle : Y / 2 ≤ 3 * Y := by linarith
  have hlogle : Real.log (1 / 2) ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  set G : ℝ → ℂ := fun y =>
    ∫ t in (-T)..T, g t * (((max y (Y / 2) : ℝ)) : ℂ) ^ ((t : ℂ) * I) with hGdef
  have hGc : Continuous G :=
    continuous_max_cpow_integral hc hg (by fun_prop) _ _
  have hGeq : ∀ y ∈ Set.uIcc (Y / 2) (3 * Y),
      ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 = ‖G y‖ ^ 2 := by
    intro y hy
    rw [Set.uIcc_of_le hle] at hy
    simp only [hGdef, max_eq_left hy.1]
  rw [intervalIntegral.integral_congr hGeq]
  -- the substitution `y = Y e^u`
  have hcov := intervalIntegral.integral_comp_mul_deriv (a := Real.log (1 / 2))
    (b := Real.log 3) (f := fun u => Y * Real.exp u) (f' := fun u => Y * Real.exp u)
    (g := fun y => ‖G y‖ ^ 2) (fun u _ => (Real.hasDerivAt_exp u).const_mul Y)
    (by fun_prop : Continuous fun u => Y * Real.exp u).continuousOn (hGc.norm.pow 2)
  have e1 : Y * Real.exp (Real.log (1 / 2)) = Y / 2 := by
    rw [Real.exp_log (by norm_num)]; ring
  have e2 : Y * Real.exp (Real.log 3) = 3 * Y := by
    rw [Real.exp_log (by norm_num)]; ring
  simp only [e1, e2] at hcov
  rw [← hcov]
  set h : ℝ → ℂ := fun t => g t * (Y : ℂ) ^ ((t : ℂ) * I) with hhdef
  have hh : Continuous h :=
    hg.mul (Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hY.ne')))
  have hnorm : ∀ t, ‖h t‖ = ‖g t‖ := by
    intro t
    simp only [hhdef, norm_mul, norm_cpow_eq_rpow_re_of_pos hY]
    simp
  set F : ℝ → ℂ := fun u => ∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I)) with hFdef
  have hFc : Continuous F := by
    have hu : Continuous fun p : ℝ × ℝ => h p.2 * cexp ((p.1 : ℂ) * ((p.2 : ℂ) * I)) :=
      (hh.comp continuous_snd).mul (Continuous.cexp (by fun_prop))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu _ _
  have hGv : ∀ u ∈ Set.Icc (Real.log (1 / 2)) (Real.log 3), G (Y * Real.exp u) = F u := by
    intro u hu
    have he : 1 / 2 ≤ Real.exp u := by
      have := Real.exp_le_exp.mpr hu.1
      rwa [Real.exp_log (by norm_num)] at this
    have hm : max (Y * Real.exp u) (Y / 2) = Y * Real.exp u := by
      apply max_eq_left
      nlinarith
    simp only [hGdef, hFdef, hm]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hhdef]
    rw [ofReal_mul_exp_cpow hY]
    ring
  have hmono : ∫ u in (Real.log (1 / 2))..(Real.log 3),
        ((fun y => ‖G y‖ ^ 2) ∘ fun u => Y * Real.exp u) u * (Y * Real.exp u) ≤
      ∫ u in (Real.log (1 / 2))..(Real.log 3), 3 * Y * ‖F u‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on hlogle
    · exact (((hGc.norm.pow 2).comp (by fun_prop : Continuous fun u => Y * Real.exp u)).mul
        (by fun_prop : Continuous fun u => Y * Real.exp u)).intervalIntegrable _ _
    · exact (continuous_const.mul (hFc.norm.pow 2)).intervalIntegrable _ _
    · intro u hu
      simp only [Function.comp_apply]
      rw [hGv u hu]
      have he : Real.exp u ≤ 3 := by
        have := Real.exp_le_exp.mpr hu.2
        rwa [Real.exp_log (by norm_num)] at this
      have hY3 : Y * Real.exp u ≤ 3 * Y := by nlinarith
      calc ‖F u‖ ^ 2 * (Y * Real.exp u) ≤ ‖F u‖ ^ 2 * (3 * Y) :=
            mul_le_mul_of_nonneg_left hY3 (by positivity)
        _ = 3 * Y * ‖F u‖ ^ 2 := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  have h2 := hK T hT h hh
  simp only [hnorm] at h2
  have hI0 : 0 ≤ 3 * Y := by positivity
  calc _ ≤ 3 * Y * ∫ u in (Real.log (1 / 2))..(Real.log 3), ‖F u‖ ^ 2 := hmono
    _ ≤ 3 * Y * (K * ∫ t in (-T)..T, ‖g t‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hI0
    _ = 3 * K * Y * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by ring

/-- Page 44, proof of Lemma 29: the lab form of the variant of [8] Lemma 2, with `y^s`,
`s = 1/2 + it`, PROVED from the printed form `leaf_gallagher_mean_value`. For `y > 0`,
`y^(1/2 + it) = y^(1/2) y^(it)` and `|y^(1/2)|^2 = y ≤ 3Y` on `[Y/2, 3Y]`. -/
theorem leaf_mellin_mean_value_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y),
          ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        K * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := leaf_gallagher_mean_value
  refine ⟨3 * K, by positivity, ?_⟩
  intro Y hY T hT g hg
  have hc : 0 < Y / 2 := by positivity
  have hle : Y / 2 ≤ 3 * Y := by linarith
  set G : ℝ → ℂ := fun y =>
    ∫ t in (-T)..T, g t * (((max y (Y / 2) : ℝ)) : ℂ) ^ ((t : ℂ) * I) with hGdef
  have hGc : Continuous G :=
    continuous_max_cpow_integral hc hg (by fun_prop) _ _
  have hFeq : ∀ y ∈ Set.uIcc (Y / 2) (3 * Y),
      ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 = y * ‖G y‖ ^ 2 := by
    intro y hy
    rw [Set.uIcc_of_le hle] at hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hm : max y (Y / 2) = y := max_eq_left hy.1
    have hsplit : ∀ t : ℝ, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
        (y : ℂ) ^ (1 / 2 : ℂ) * (g t * (y : ℂ) ^ ((t : ℂ) * I)) := by
      intro t
      rw [cpow_add _ _ (ofReal_ne_zero.mpr hy0.ne')]
      ring
    simp only [hGdef, hm]
    simp_rw [hsplit]
    rw [intervalIntegral.integral_const_mul, norm_mul, mul_pow,
      norm_cpow_eq_rpow_re_of_pos hy0]
    congr 1
    have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  have hGeq : ∀ y ∈ Set.uIcc (Y / 2) (3 * Y),
      ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 = ‖G y‖ ^ 2 := by
    intro y hy
    rw [Set.uIcc_of_le hle] at hy
    simp only [hGdef, max_eq_left hy.1]
  rw [intervalIntegral.integral_congr hFeq]
  have h1 := hK Y hY T hT g hg
  rw [intervalIntegral.integral_congr hGeq] at h1
  have hmono : ∫ y in (Y / 2)..(3 * Y), y * ‖G y‖ ^ 2 ≤
      ∫ y in (Y / 2)..(3 * Y), 3 * Y * ‖G y‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on hle
    · exact (continuous_id.mul (hGc.norm.pow 2)).intervalIntegrable _ _
    · exact (continuous_const.mul (hGc.norm.pow 2)).intervalIntegrable _ _
    · intro y hy
      exact mul_le_mul_of_nonneg_right hy.2 (by positivity)
  rw [intervalIntegral.integral_const_mul] at hmono
  have hI0 : 0 ≤ 3 * Y := by positivity
  calc _ ≤ 3 * Y * ∫ y in (Y / 2)..(3 * Y), ‖G y‖ ^ 2 := hmono
    _ ≤ 3 * Y * (K * Y * ∫ t in (-T)..T, ‖g t‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hI0
    _ = 3 * K * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by ring

end LeanLab.BHP1997.MellinCore

#print axioms LeanLab.BHP1997.MellinCore.leaf_mellin_mean_value_of_leaves
