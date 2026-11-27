/-
Route burst burst-20261124, session S4, unit S4-28, BHP1997, split of
`S64LowExcCharNP.leaf_mellin_mean_value` in S64LowExcCharNonprincipal.lean.

P0069 Baker Harman Pintz 1997, page 44, proof of Lemma 29: "By a variant of [8], Lemma 2,
`∫_{Y/2}^{3Y} |∫_T^{T'} g(t) y^(it) dt|^2 dy ≪ Y L ∫_T^{T'} |g(t)|^2 dt` whenever `g` is
continuous". The lab leaf keeps the factor `y^(1/2)` of `y^s`, `s = 1/2 + it`, inside the
inner integral. This file separates the two steps:
* `leaf_gallagher_mean_value`: the printed display itself, with `y^(it)`, the range `[-T, T]`
  and without the factor `L`, exactly as QUESTION 1 of the S64 note reads it. CITED [8]
  Lemma 2, Gallagher 1970; it holds by Plancherel after `y = e^u`.
* `leaf_mellin_mean_value_of_leaves`: PROVED from that leaf. For `y > 0`,
  `y^(1/2 + it) = y^(1/2) y^(it)`, so the square of the inner integral is `y` times the square
  of the printed inner integral, and `y ≤ 3Y` on the range, which turns `Y` into `Y^2`.
`leaf_mellin_mean_value_split_twin` checks the exact statement of the S64 leaf.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.S64LowExcCharNonprincipal

namespace LeanLab.BHP1997.S64LowExcCharNP
open Complex MeasureTheory

/-- LEAF: page 44, proof of Lemma 29, the variant of [8] Lemma 2 as printed, class HARD.
P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2,
`∫_{Y/2}^{3Y} |∫_T^{T'} g(t) y^(it) dt|^2 dy ≪ Y L ∫_T^{T'} |g(t)|^2 dt` whenever `g` is
continuous", on the symmetric range `[-T, T]` used on page 44 and in the form without the
factor `L`, which holds by Plancherel after `y = e^u` with an absolute constant, QUESTION 1
of the S64 note. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gallagher_mean_value :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y), ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 ≤
        K * Y * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  sorry

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

/-- The split closes exactly the statement of `leaf_mellin_mean_value`. -/
theorem leaf_mellin_mean_value_split_twin :
    type_of% @leaf_mellin_mean_value :=
  leaf_mellin_mean_value_of_leaves

end LeanLab.BHP1997.S64LowExcCharNP

#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_mellin_mean_value_of_leaves
#print axioms LeanLab.BHP1997.S64LowExcCharNP.continuous_max_cpow_integral
