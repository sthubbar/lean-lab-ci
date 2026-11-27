/-
Route burst burst-20261124, session S4, KEEP GOING after unit S4-28, BHP1997, split of
`S64LowExcCharNP.leaf_gallagher_mean_value` in SPLIT_leaf_mellin_mean_value.lean.

P0069 Baker Harman Pintz 1997, page 44, proof of Lemma 29, the variant of [8] Lemma 2,
`∫_{Y/2}^{3Y} |∫ g(t) y^(it) dt|^2 dy ≪ Y ∫ |g(t)|^2 dt`. Its proof, after QUESTION 1 of
the S64 note, is the substitution `y = e^u` followed by Plancherel. This file separates them:
* `leaf_plancherel_log_window`: the scale free form on the fixed window
  `u ∈ [log(1/2), log 3]`, the Fourier side of Gallagher's Lemma 2. CITED [8] Lemma 2,
  Gallagher 1970, Plancherel.
* `leaf_gallagher_mean_value_of_leaves`: PROVED from that leaf by the substitution
  `y = Y e^u`, with `dy = Y e^u du ≤ 3Y du` and `y^(it) = Y^(it) e^(itu)`, where the factor
  `Y^(it)` has modulus one and is absorbed into `g`.
`leaf_gallagher_mean_value_split_twin` checks the exact statement of the earlier leaf.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.SPLIT_leaf_mellin_mean_value

namespace LeanLab.BHP1997.S64LowExcCharNP
open Complex MeasureTheory

/-- LEAF: page 44, proof of Lemma 29, the Fourier side of the variant of [8] Lemma 2 after
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
  sorry

/-- Standard complex analysis. For `Y > 0`, `(Y e^u)^(it) = Y^(it) e^(itu)`. -/
theorem ofReal_mul_exp_cpow {Y : ℝ} (hY : 0 < Y) (u t : ℝ) :
    (((Y * Real.exp u : ℝ)) : ℂ) ^ ((t : ℂ) * I) =
      (Y : ℂ) ^ ((t : ℂ) * I) * cexp ((u : ℂ) * ((t : ℂ) * I)) := by
  rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg hY.le (Real.exp_pos u).le]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]

/-- Page 44, proof of Lemma 29: the variant of [8] Lemma 2 in the `y` variable, PROVED from
`leaf_plancherel_log_window` by the substitution `y = Y e^u`. -/
theorem leaf_gallagher_mean_value_of_leaves :
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

/-- The split closes exactly the statement of `leaf_gallagher_mean_value`. -/
theorem leaf_gallagher_mean_value_split_twin :
    type_of% @leaf_gallagher_mean_value :=
  leaf_gallagher_mean_value_of_leaves

end LeanLab.BHP1997.S64LowExcCharNP

#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gallagher_mean_value_of_leaves
#print axioms LeanLab.BHP1997.S64LowExcCharNP.ofReal_mul_exp_cpow
