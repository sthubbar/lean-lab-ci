/-
Route burst burst-20261124, session S4, unit S4-28, BHP1997: the statement of
`S64LowExcCharNP.leaf_mellin_mean_value` in S64LowExcCharNonprincipal.lean with no sorry.

P0069 Baker Harman Pintz 1997, page 44, proof of Lemma 29, "By a variant of [8], Lemma 2".
The split chain of this burst, SPLIT_leaf_mellin_mean_value, SPLIT_leaf_gallagher_mean_value,
SPLIT_leaf_plancherel_log_window, SPLIT_leaf_gaussian_weighted_mean_value and
SPLIT_leaf_gaussian_expansion, proves each leaf from the next one in a later file, and the
last two files are now free of sorry. Each assembly names the leaf constant of its own file,
so the chain is closed here by repeating the three assemblies verbatim with the proved
statement in place of the leaf:
* `leaf_plancherel_log_window_proved`, from `leaf_gaussian_weighted_mean_value_of_leaves`;
* `leaf_gallagher_mean_value_proved`, from it, by `y = Y e^u`;
* `leaf_mellin_mean_value_proved`, from it, by `y^(1/2+it) = y^(1/2) y^(it)`, with exactly
  the type of `leaf_mellin_mean_value`, checked by `leaf_mellin_mean_value_proved_twin`.
The sorry in S64LowExcCharNonprincipal.lean itself stays, since that file is imported by the
chain and cannot import it back.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.SPLIT_leaf_gaussian_weighted_mean_value

namespace LeanLab.BHP1997.S64LowExcCharNP
open Complex MeasureTheory

/-- Page 44, proof of Lemma 29: the scale free variant of [8] Lemma 2 on the window
`[log(1/2), log 3]`, PROVED with no sorry; the proof of
`leaf_plancherel_log_window_of_leaves` with the proved Gaussian weighted mean value. -/
theorem leaf_plancherel_log_window_proved :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ h : ℝ → ℂ, Continuous h →
      ∫ u in (Real.log (1 / 2))..(Real.log 3),
          ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 ≤
        K * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := leaf_gaussian_weighted_mean_value_of_leaves
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

/-- Page 44, proof of Lemma 29: the printed variant of [8] Lemma 2 without the factor `L`,
PROVED with no sorry; the proof of `leaf_gallagher_mean_value_of_leaves` with the proved
window form. -/
theorem leaf_gallagher_mean_value_proved :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y), ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 ≤
        K * Y * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := leaf_plancherel_log_window_proved
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

/-- Page 44, proof of Lemma 29: the lab form of the variant of [8] Lemma 2 with `y^s`,
PROVED with no sorry; the proof of `leaf_mellin_mean_value_of_leaves` with the proved
printed form. -/
theorem leaf_mellin_mean_value_proved :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y),
          ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        K * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := leaf_gallagher_mean_value_proved
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

/-- Exactly the statement of `leaf_mellin_mean_value`, with no sorry. -/
theorem leaf_mellin_mean_value_proved_twin :
    type_of% @leaf_mellin_mean_value :=
  leaf_mellin_mean_value_proved

end LeanLab.BHP1997.S64LowExcCharNP

#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_plancherel_log_window_proved
#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gallagher_mean_value_proved
#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_mellin_mean_value_proved_twin
