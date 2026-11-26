import LeanLab.HelfgottMajor.SPLIT_border_logDeriv_le_of_one_le_re
import LeanLab.HelfgottMajor.SPLIT_vonMangoldt_tsum_eleven_tenths_le

/-!
# Split of `border_principal_logDeriv_le_of_one_le_re` (`HelfgottMajor/SPLIT_border_logDeriv_le_of_one_le_re`)

The target, a MEDIUM leaf of the burst-20261124 split S2-05, bounds `‖g'/g‖` by `11.7` for
`g(s) = (s - 1) ζ(s)`, Mathlib's `LFunctionTrivChar₁ 1`, on the part `1 ≤ Re u` of the border of
the box `[-1/4, 5/4] x [-3/2, 3/2]`.  The cut is at `Re u = 6/5`:

* on `6/5 ≤ Re u`, `g'/g = 1/(u - 1) + ζ'/ζ(u)` for `u ≠ 1`, proved, so
  `‖g'/g‖ ≤ 5 + ∑ Λ(n) n^{-6/5}`; the series is at most `1.03883 ζ(6/5) ≤ 1.03883 · 6` by the
  Rosser and Schoenfeld leaf and the Abel summation lemma of
  `SPLIT_vonMangoldt_tsum_eleven_tenths_le`, and `ζ(6/5) ≤ 6` is proved here by the integral
  comparison; `5 + 6.233 ≤ 11.7`.  This uses no new leaf.
* on `1 ≤ Re u ≤ 6/5`, which on this border are the two short horizontal pieces at height
  `± 3/2`, the series does not converge absolutely at `Re u = 1`; this is the new leaf
  `border_principal_logDeriv_le_near_one`, a numerical fact about `ζ` near `1 ± 3i/2`.
  mpmath gives a maximum of `0.5364` there.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/


namespace LeanLab.HelfgottMajor.SplitPrincipalBorder

open Real Finset
open LeanLab.HelfgottArcs Decomp269a Decomp269b
open LeanLab.HelfgottMajor.SplitStripCount LeanLab.HelfgottMajor.SplitVonMangoldtTsum

open Set MeasureTheory in
/-- `ζ(6/5) ≤ 6`, proved, from the integral comparison `ζ(σ) ≤ 1 + 1/(σ - 1)` at `σ = 6/5`, Mathlib
`AntitoneOn.abs_tsum_sub_sum_range_le_integral`; the true value is `5.5915...`. -/
theorem tsum_one_div_rpow_six_fifths_le :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (6 / 5 : ℝ) ≤ 6 := by
  set f : ℝ → ℝ := fun x => 1 / x ^ (6 / 5 : ℝ) with hf
  have hEq : EqOn f (fun x : ℝ => x ^ (-(6 / 5) : ℝ)) (Ioi ((2 : ℕ) - 1 : ℝ)) := by
    intro x hx
    simp only [hf, rpow_neg (le_of_lt (lt_trans one_pos (by norm_num at hx ⊢; linarith))),
      one_div]
  have hpos : (0 : ℝ) < ((2 : ℕ) - 1 : ℝ) := by norm_num
  have hint : IntegrableOn f (Ioi ((2 : ℕ) - 1 : ℝ)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -(6/5)) (by norm_num) hpos).congr_fun ?_
      measurableSet_Ioi
    exact fun x hx => (hEq hx).symm
  have hanti : AntitoneOn f (Ici ((2 : ℕ) - 1 : ℝ)) := by
    intro x hx y hy hxy
    have hx1 : (1 : ℝ) ≤ x := by norm_num at hx; linarith
    have hx0 : 0 < x := by linarith
    simp only [hf]
    apply one_div_le_one_div_of_le (rpow_pos_of_pos hx0 _)
    exact rpow_le_rpow hx0.le hxy (by norm_num)
  have hnn : ∀ t ∈ Ioi ((2 : ℕ) - 1 : ℝ), 0 ≤ f t := by
    intro t ht
    have : (0:ℝ) < t := lt_trans hpos ht
    simp only [hf]; positivity
  have h := hanti.abs_tsum_sub_sum_range_le_integral (N := 2) (by norm_num) hint hnn
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq,
    integral_Ioi_rpow_of_lt (by norm_num) hpos] at h
  have hs : ∑ n ∈ Finset.range 2, f n = 1 := by
    simp [hf, Finset.sum_range_succ]
  rw [hs] at h
  have h3 : -((2 : ℕ) - 1 : ℝ) ^ (-(6 / 5) + 1 : ℝ) / (-(6 / 5) + 1) = 5 := by norm_num
  rw [h3] at h
  have := (abs_le.mp h).2
  simp only [hf] at this
  linarith

/-- `-ζ'/ζ(σ) = ∑ Λ(n) n^{-σ} ≤ 1.03883 · 6` on `6/5 ≤ σ`, from the Rosser and Schoenfeld leaf
`psi_le_rosser_schoenfeld`, the proved Abel summation lemma and `ζ(6/5) ≤ 6`. -/
theorem vonMangoldt_tsum_le_of_six_fifths_le (σ : ℝ) (hσ : 6 / 5 ≤ σ) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ ≤ 1.03883 * 6 := by
  have hA : ∀ N : ℕ, ∑ n ∈ Ioc 0 N, (ArithmeticFunction.vonMangoldt n : ℝ) ≤
      1.03883 * (N : ℝ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have h := psi_le_rosser_schoenfeld N (by exact_mod_cast hN)
      rwa [Chebyshev.psi, Nat.floor_natCast] at h
  have h1 := tsum_div_rpow_le_of_partial_sums_le _
    (fun n => ArithmeticFunction.vonMangoldt_nonneg) 1.03883 (6 / 5) (by norm_num) hA
  have h2 := tsum_one_div_rpow_six_fifths_le
  refine le_trans ?_ (h1.trans (by nlinarith))
  refine Summable.tsum_le_tsum (fun n => ?_) (vonMangoldt_real_summable (by linarith))
    (vonMangoldt_real_summable (by norm_num))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · apply div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hσ

/-- For `1 < Re u`, the logarithmic derivative of `(s - 1) ζ(s)` splits as
`1/(u - 1) + L'/L(u)` with `L = L(s, 1 mod 1) = ζ`, proved from Mathlib's
`deriv_LFunctionTrivChar₁_apply_of_ne_one` and `LFunction_ne_zero_of_one_le_re`. -/
theorem logDeriv_LFunctionTrivChar₁_one_eq {u : ℂ} (hu : 1 < u.re) :
    logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) u =
      1 / (u - 1) + logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) u := by
  have hu1 : u ≠ 1 := by rintro rfl; norm_num at hu
  have hsub : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) u ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (.inr hu1) hu.le
  rw [logDeriv_apply, logDeriv_apply,
    DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hu1]
  have hv : DirichletCharacter.LFunctionTrivChar₁ 1 u =
      (u - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) u :=
    Function.update_of_ne hu1 _ _
  rw [hv]
  field_simp
  ring

/-- The bound of the target on `6/5 ≤ Re u`: `‖1/(u - 1)‖ ≤ 5` and `‖ζ'/ζ(u)‖ ≤ 1.03883 · 6`.
Uses the Rosser and Schoenfeld leaf only. -/
theorem norm_logDeriv_LFunctionTrivChar₁_one_le {u : ℂ} (hu : 6 / 5 ≤ u.re) :
    ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) u‖ ≤ 11.7 := by
  have hu1 : 1 < u.re := by linarith
  rw [logDeriv_LFunctionTrivChar₁_one_eq hu1]
  have hA := norm_logDeriv_LFunction_le_vonMangoldt_tsum (1 : DirichletCharacter ℂ 1) hu1
  have hB := vonMangoldt_tsum_le_of_six_fifths_le u.re hu
  have hC : ‖1 / (u - 1)‖ ≤ 5 := by
    have hre : (1 : ℝ) / 5 ≤ ‖u - 1‖ := by
      have := Complex.abs_re_le_norm (u - 1)
      rw [Complex.sub_re, Complex.one_re, abs_of_pos (by linarith)] at this
      linarith
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  calc _ ≤ ‖1 / (u - 1)‖ + _ := norm_add_le _ _
    _ ≤ 5 + 1.03883 * 6 := add_le_add hC (hA.trans hB)
    _ ≤ 11.7 := by norm_num

/-- LEAF: the short horizontal pieces `1 ≤ Re u ≤ 6/5`, `Im u = ±3/2`, of the border for
`g(s) = (s - 1) ζ(s)`, MEDIUM: a numerical fact about `ζ` at small height near `Re s = 1`, where
`ζ` has no zero; provable by an explicit Euler Maclaurin evaluation of `ζ` and `ζ'` on the two
segments.  mpmath gives a maximum of `0.5364` for `‖g'/g‖` there. -/
theorem border_principal_logDeriv_le_near_one :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      1 ≤ u.re → u.re ≤ 6 / 5 →
      ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) u‖ ≤ 11.7 := by
  sorry

/-- The parent leaf `border_principal_logDeriv_le_of_one_le_re`, verbatim, from the leaf above
and the proved bound on `6/5 ≤ Re u`, which rests on the Rosser and Schoenfeld leaf. -/
theorem border_principal_logDeriv_le_of_one_le_re_split :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      1 ≤ u.re → ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) u‖ ≤ 11.7 := by
  intro u hu h1
  by_cases h2 : u.re ≤ 6 / 5
  · exact border_principal_logDeriv_le_near_one u hu h1 h2
  · exact norm_logDeriv_LFunctionTrivChar₁_one_le (not_le.mp h2).le

end LeanLab.HelfgottMajor.SplitPrincipalBorder
