/-
Route burst burst-20261124, session S4, KEEP GOING after unit S4-28, BHP1997, split of
`S64LowExcCharNP.leaf_gaussian_expansion` in SPLIT_leaf_gaussian_weighted_mean_value.lean.

P0069 Baker Harman Pintz 1997, page 44, proof of Lemma 29, the variant of [8] Lemma 2 with
the Gaussian weight `w(u) = exp(-u^2/4)`, Gallagher's first step, in two pieces:
* `leaf_gaussian_fubini`, PROVED by S4 KEEP GOING after a clamp of `h` to `[-T, T]`: `|F(u)|^2 = F(u) conj F(u)` is the double integral of
  `h(t) conj h(s) e^(iu(t-s))`, and the `u` integral moves inside by Fubini.
* `gaussian_fourier`: PROVED from Mathlib `integral_cexp_quadratic`, the Fourier transform
  `∫ w(u) e^(iux) du = 2 √π exp(-x^2)`.
* `leaf_gaussian_expansion_of_leaves`: PROVED from the two, exactly the statement of
  `leaf_gaussian_expansion`, which SPLIT_leaf_gaussian_weighted_mean_value.lean now proves
  by importing this file.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.SPLIT_leaf_plancherel_log_window

namespace LeanLab.BHP1997.S64LowExcCharNP
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

/-- Page 44, proof of Lemma 29: Gallagher's expansion with the Gaussian weight, PROVED from
`leaf_gaussian_fubini` and `gaussian_fourier`, exactly the statement of
`leaf_gaussian_expansion`. -/
theorem leaf_gaussian_expansion_of_leaves (T : ℝ) (hT : 0 ≤ T) (h : ℝ → ℂ)
    (hh : Continuous h) :
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

end LeanLab.BHP1997.S64LowExcCharNP

#print axioms LeanLab.BHP1997.S64LowExcCharNP.gaussian_fourier
#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gaussian_fubini
#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gaussian_expansion_of_leaves
