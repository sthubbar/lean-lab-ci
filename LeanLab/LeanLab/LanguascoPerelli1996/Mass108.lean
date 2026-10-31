import LeanLab.LanguascoPerelli1996.Correlation108

/-!
The local mass step in P0071 page 355 display 12.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Mass108
open Real MeasureTheory intervalIntegral

/-- Page 354 definition of G. A zero band is the difference of two full zero sums. -/
theorem zSum_band_eq_sub (y U T : ℝ) (hUT : U ≤ T)
    (q : ℕ) [NeZero q] (a : ℕ) :
    zSum y U T q a = zSum y (-1) T q a - zSum y (-1) U q a := by
  classical
  have hneg : {ρ : ℂ | |ρ.im| ≤ (-1 : ℝ)} = ∅ := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    linarith [abs_nonneg ρ.im]
  have hsplit (χ : DirichletCharacter ℂ q) :
      (∑ᶠ ρ ∈ ntZeros χ T \ {ρ | |ρ.im| ≤ U},
        (mult χ ρ : ℂ) * Complex.exp (Complex.I * (ρ.im : ℂ) * (Real.log y : ℂ))) =
      (∑ᶠ ρ ∈ ntZeros χ T,
        (mult χ ρ : ℂ) * Complex.exp (Complex.I * (ρ.im : ℂ) * (Real.log y : ℂ))) -
      (∑ᶠ ρ ∈ ntZeros χ U,
        (mult χ ρ : ℂ) * Complex.exp (Complex.I * (ρ.im : ℂ) * (Real.log y : ℂ))) := by
    have hinter : ntZeros χ T ∩ {ρ | |ρ.im| ≤ U} = ntZeros χ U := by
      ext ρ
      simp only [ntZeros, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h0, h1, h2, _⟩, hu⟩
        exact ⟨h0, h1, h2, hu⟩
      · rintro ⟨h0, h1, h2, hu⟩
        exact ⟨⟨h0, h1, h2, hu.trans hUT⟩, hu⟩
    have hh := finsum_mem_inter_add_sdiff (f := fun ρ : ℂ =>
      (mult χ ρ : ℂ) * Complex.exp (Complex.I * (ρ.im : ℂ) * (Real.log y : ℂ)))
      {ρ | |ρ.im| ≤ U} (Zeros108.ntZeros_finite χ T)
    rw [hinter] at hh
    exact eq_sub_of_add_eq' hh
  unfold zSum
  simp only [hneg, Set.sdiff_empty]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hsplit, mul_sub]

/-- Page 354 display 11 and page 355 display 12.
On minus one to one a nonnegative mass is at most exp 2 times its full weighted mass. -/
theorem local_mass_le_weighted {g : ℝ → ℝ} (hg : Continuous g) (hpos : ∀ v, 0 ≤ g v)
    (hi : Integrable (fun v => g v * Real.exp (-2 * |v|))) :
    (∫ v in (-1 : ℝ)..1, g v) ≤ Real.exp 2 * ∫ v : ℝ, g v * Real.exp (-2 * |v|) := by
  have hc : Continuous (fun v => g v * Real.exp (-2 * |v|)) := by fun_prop
  have hm : (∫ v in (-1 : ℝ)..1, g v) ≤
      ∫ v in (-1 : ℝ)..1, Real.exp 2 * (g v * Real.exp (-2 * |v|)) := by
    apply integral_mono_on (by norm_num) (hg.intervalIntegrable _ _)
      ((continuous_const.mul hc).intervalIntegrable _ _)
    intro v hv
    simp only [Pi.mul_apply, Pi.add_apply]
    have hvabs : |v| ≤ 1 := abs_le.mpr hv
    have he : 1 ≤ Real.exp 2 * Real.exp (-2 * |v|) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      linarith
    nlinarith [mul_le_mul_of_nonneg_left he (hpos v)]
  rw [intervalIntegral.integral_const_mul] at hm
  have hall : (∫ v in (-1 : ℝ)..1, g v * Real.exp (-2 * |v|)) ≤
      ∫ v : ℝ, g v * Real.exp (-2 * |v|) := by
    rw [integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun v =>
      mul_nonneg (hpos v) (Real.exp_pos _).le)
  exact hm.trans (mul_le_mul_of_nonneg_left hall (Real.exp_pos 2).le)

/-- Page 354 display 11. The weighted full mass is the norm of the sealed F. -/
theorem full_weighted_mass {X : ℝ} (hX : 0 < X) (T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    (∫ v : ℝ, ‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 * Real.exp (-2 * |v|)) =
      ‖F X T q a‖ := by
  have he := (Correlation108.correlation_identity hX T q a).2
  have hpos : 0 ≤ ∫ v : ℝ, ‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 * Real.exp (-2 * |v|) :=
    integral_nonneg fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hn := congrArg norm he
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] using hn

/-- LEAF. Pages 354 and 355, displays 11 and 12.
The local band mass is at most 2 exp 2 times the sum of the two correlations. -/
theorem band_local_mass {X : ℝ} (hX : 0 < X) (U T : ℝ) (hUT : U ≤ T)
    (q : ℕ) [NeZero q] (a : ℕ) :
    (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) ≤
      (2 * Real.exp 2) * (‖F X T q a‖ + ‖F X U q a‖) := by
  have hlocal (t : ℝ) : (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) (-1) t q a‖ ^ 2) ≤
      Real.exp 2 * ‖F X t q a‖ := by
    rw [← full_weighted_mass hX t q a]
    exact local_mass_le_weighted (Band108.energy_contDiff hX (-1) t q a).continuous
      (fun v => sq_nonneg _) (Correlation108.correlation_identity hX t q a).1
  have hc (u t : ℝ) : Continuous (fun v => ‖zSum (X * Real.exp v) u t q a‖ ^ 2) :=
    (Band108.energy_contDiff hX u t q a).continuous
  have hm : (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) ≤
      ∫ v in (-1 : ℝ)..1, 2 * (‖zSum (X * Real.exp v) (-1) T q a‖ ^ 2 +
        ‖zSum (X * Real.exp v) (-1) U q a‖ ^ 2) := by
    apply integral_mono_on (by norm_num) ((hc U T).intervalIntegrable _ _)
      ((continuous_const.mul ((hc (-1) T).add (hc (-1) U))).intervalIntegrable _ _)
    intro v hv
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [zSum_band_eq_sub _ _ _ hUT]
    have hnorm := norm_sub_le (zSum (X * Real.exp v) (-1) T q a)
      (zSum (X * Real.exp v) (-1) U q a)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (‖zSum (X * Real.exp v) (-1) T q a‖ -
      ‖zSum (X * Real.exp v) (-1) U q a‖)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add ((hc (-1) T).intervalIntegrable _ _)
    ((hc (-1) U).intervalIntegrable _ _)] at hm
  nlinarith [hlocal T, hlocal U]

end LeanLab.LanguascoPerelli1996.Mass108
