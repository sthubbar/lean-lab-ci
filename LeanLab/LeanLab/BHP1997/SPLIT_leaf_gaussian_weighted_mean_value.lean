/-
Route burst burst-20261124, session S4, KEEP GOING after unit S4-28, BHP1997, split of
`S64LowExcCharNP.leaf_gaussian_weighted_mean_value` in SPLIT_leaf_plancherel_log_window.lean.

P0069 Baker Harman Pintz 1997, page 44, proof of Lemma 29, the variant of [8] Lemma 2 with
the Gaussian weight `w(u) = exp(-u^2/4)`. Gallagher's argument has two steps:
* `leaf_gaussian_expansion`, PROVED by S4 KEEP GOING from SPLIT_leaf_gaussian_expansion.lean: expanding `|F(u)|^2 = F(u) conj F(u)` and integrating in `u`
  first, the weighted mean value is the double integral of `h(t) conj h(s)` against the
  Fourier transform of `w`, which is `2 √π exp(-(t-s)^2)`. Fubini and the Gaussian integral.
* `leaf_gaussian_kernel_schur`, PROVED here by S4 KEEP GOING: the double integral is at most `2π ∫ |h|^2`, by
  `|h(t) h(s)| ≤ (|h(t)|^2 + |h(s)|^2)/2` and `∫_ℝ 2 √π exp(-x^2) dx = 2π`.
* `leaf_gaussian_weighted_mean_value_of_leaves`: PROVED from the two leaves with `K = 2π`.
`leaf_gaussian_weighted_mean_value_split_twin` checks the exact statement of the earlier leaf.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.SPLIT_leaf_gaussian_expansion

namespace LeanLab.BHP1997.S64LowExcCharNP
open Complex MeasureTheory

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
  exact leaf_gaussian_expansion_of_leaves T hT h hh

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

/-- Page 44, proof of Lemma 29: the Gaussian weighted variant of [8] Lemma 2, PROVED from
`leaf_gaussian_expansion` and `leaf_gaussian_kernel_schur` with `K = 2π`: the weighted
mean value is a real number at most the modulus of the double integral. -/
theorem leaf_gaussian_weighted_mean_value_of_leaves :
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

/-- The split closes exactly the statement of `leaf_gaussian_weighted_mean_value`. -/
theorem leaf_gaussian_weighted_mean_value_split_twin :
    type_of% @leaf_gaussian_weighted_mean_value :=
  leaf_gaussian_weighted_mean_value_of_leaves

end LeanLab.BHP1997.S64LowExcCharNP

#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gaussian_weighted_mean_value_of_leaves
#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gaussian_kernel_schur
#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gaussian_expansion
#print axioms LeanLab.BHP1997.S64LowExcCharNP.interval_integral_swap_of_continuous
#print axioms LeanLab.BHP1997.S64LowExcCharNP.gaussian_kernel_interval_le
