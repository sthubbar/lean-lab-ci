import LeanLab.HelfgottMajor.SPLIT_strip_count_at_one_le_explicit

/-!
# Split of `border_logDeriv_le_of_one_le_re` (`HelfgottMajor/SPLIT_border_norm_logDeriv_le`)

The target bounds `‖g'/g‖` by `0.5 log q + 11.7` on the part of the border of the box
`[-1/4, 5/4] x [-3/2, 3/2]` with `1 ≤ Re u`, where `g` is `L(s, χ)` for a nontrivial primitive
`χ` and the pole removed `(s - 1) ζ(s)` for the trivial one.  That part of the border is the
right side `Re u = 5/4` together with the two short pieces `1 ≤ Re u ≤ 5/4`, `Im u = ±3/2`.

The cut separates the three mechanisms at work:

* the trivial character, where primitivity forces `q = 1` and `g` is `(s - 1) ζ(s)`; this is a
  fixed function and the bound is a numerical fact about `ζ` at small height, leaf
  `border_principal_logDeriv_le_of_one_le_re`;
* the region `11/10 ≤ Re u` for a nontrivial character, where `L'/L` is the absolutely
  convergent twisted von Mangoldt series, so `‖L'/L(u)‖ ≤ -ζ'/ζ(Re u)`.  This comparison is
  proved below as `norm_logDeriv_LFunction_le_vonMangoldt_tsum`, from Mathlib's
  `LSeries_twist_vonMangoldt_eq`; the series decreases in `Re u`, proved, and what remains is the
  numerical value `-ζ'/ζ(11/10) = 9.441...`, leaf `vonMangoldt_tsum_eleven_tenths_le`;
* the short pieces `1 ≤ Re u ≤ 11/10`, `Im u = ±3/2`, for a nontrivial character, where the
  series does not converge absolutely.  Note the doc comment of the parent leaf claims absolute
  convergence on all of `1 ≤ Re u`; that is wrong at `Re u = 1`, and this piece needs an
  explicit zero free region, leaf `border_nonprincipal_logDeriv_le_near_one`.

The assembly `border_logDeriv_le_of_one_le_re_split` proves the parent leaf statement from the
three leaves and the proved comparison, with nothing else.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitStripCount

open Real MeasureTheory Set Filter
open scoped Topology LSeries.notation
open LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- On `1 < Re s` the logarithmic derivative of `L(s, χ)` is minus the `L`-series of the twist
`χ Λ`, Davenport, Multiplicative Number Theory, chapter 12, and so its norm is at most the
series `∑ Λ(n) n^{-Re s} = -ζ'/ζ(Re s)`, since `‖χ(n)‖ ≤ 1`.  Proved from Mathlib's
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`; no hypothesis on `χ`. -/
theorem norm_logDeriv_LFunction_le_vonMangoldt_tsum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s.re := by
  have hU : {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have hEq : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries (fun n => χ n) := by
    filter_upwards [hU] with z hz using DirichletCharacter.LFunction_eq_LSeries χ hz
  have hlog : logDeriv (DirichletCharacter.LFunction χ) s =
      -LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) s := by
    rw [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, neg_div, neg_neg]
  rw [hlog, norm_neg]
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hΛ : LSeriesSummable ↗ArithmeticFunction.vonMangoldt (s.re : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hs)
  have hR : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s.re) =
      fun n => ‖LSeries.term ↗ArithmeticFunction.vonMangoldt (s.re : ℂ) n‖ := by
    funext n
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [if_neg hn, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg
        ArithmeticFunction.vonMangoldt_nonneg]
  rw [hR]
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) hsum.norm hΛ.norm
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, if_neg hn, Complex.ofReal_re]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

/-- LEAF: the value of `-ζ'/ζ` at `11/10`, a numerical fact, classical, see Davenport chapter 12
for `-ζ'/ζ(σ) = ∑ Λ(n) n^{-σ}` on `σ > 1`; its value at `11/10` is `9.4410...` by mpmath.
MEDIUM: an explicit Chebyshev bound `ψ(x) ≤ 1.04 x`, Rosser and Schoenfeld 1962, by partial
summation gives `∑ Λ(n) n^{-σ} ≤ 1.04 σ / (σ - 1) = 11.44` at `σ = 11/10`. -/
theorem vonMangoldt_tsum_eleven_tenths_le :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (11 / 10 : ℝ) ≤ 11.7 := by
  sorry

/-- The real series `∑ Λ(n) n^{-σ}` converges on `σ > 1`, from Mathlib's
`ArithmeticFunction.LSeriesSummable_vonMangoldt`. -/
theorem vonMangoldt_real_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) := by
  have hΛ : LSeriesSummable ↗ArithmeticFunction.vonMangoldt (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  refine hΛ.norm.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg
      ArithmeticFunction.vonMangoldt_nonneg]

/-- The series `∑ Λ(n) n^{-σ} = -ζ'/ζ(σ)` decreases in `σ`, so on `11/10 ≤ σ` it is at most its
value at `11/10`, which the leaf `vonMangoldt_tsum_eleven_tenths_le` bounds by `11.7`. -/
theorem vonMangoldt_tsum_le_of_eleven_tenths_le (σ : ℝ) (hσ : 11 / 10 ≤ σ) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ ≤ 11.7 := by
  refine le_trans ?_ vonMangoldt_tsum_eleven_tenths_le
  refine Summable.tsum_le_tsum (fun n => ?_) (vonMangoldt_real_summable (by linarith))
    (vonMangoldt_real_summable (by norm_num))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · apply div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hσ

/-- LEAF: the trivial character on the part `1 ≤ Re u` of the border, where primitivity forces
`q = 1` and `g(s) = (s - 1) ζ(s)`, so `g'/g = 1/(s - 1) + ζ'/ζ(s)`; the bound `11.7` of the
parent with `log 1 = 0` is a numerical fact about `ζ` below height `3/2` near `Re s = 1`, where
`ζ` has no zero.  mpmath gives a maximum of `0.537` for `‖g'/g‖` on this part of the border.
MEDIUM. -/
theorem border_principal_logDeriv_le_of_one_le_re :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      1 ≤ u.re → ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) u‖ ≤ 11.7 := by
  sorry

/-- LEAF: the short horizontal pieces `1 ≤ Re u ≤ 11/10`, `Im u = ±3/2`, for a nontrivial
primitive character, the part of the parent border step where the prime sum is not absolutely
convergent.  It needs an explicit zero free region for `L(s, χ)` near `1 ± 3i/2` together with a
Landau or Borel Caratheodory bound for `L'/L`, Montgomery and Vaughan Theorem 11.4 in the
`O(log q)` form, here with the explicit coefficient `0.5`.  For prime moduli up to `211` the
maximum of `‖L'/L‖` on this part is about `2.03`, see the feed1122 note.  HARD: whether the
coefficient `0.5` is known unconditionally for all `q` is a QUESTION. -/
theorem border_nonprincipal_logDeriv_le_near_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      1 ≤ u.re → u.re ≤ 11 / 10 →
      ‖logDeriv (DirichletCharacter.LFunction χ) u‖ ≤ 0.5 * log q + 11.7 := by
  sorry

/-! ### The assembly -/

/-- The parent leaf `border_logDeriv_le_of_one_le_re`, proved from the three leaves above and
the comparison `norm_logDeriv_LFunction_le_vonMangoldt_tsum`. -/
theorem border_logDeriv_le_of_one_le_re_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      1 ≤ u.re →
      ‖logDeriv (fun s => if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
        else DirichletCharacter.LFunction χ s) u‖ ≤ 0.5 * log q + 11.7 := by
  intro u hu h1
  by_cases hχ1 : χ = 1
  · have hq : q = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, hχ1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hq
    simp only [hχ1, ite_true, Nat.cast_one, Real.log_one, mul_zero, zero_add]
    exact border_principal_logDeriv_le_of_one_le_re u hu h1
  · simp only [hχ1, ite_false]
    have hlogq : 0 ≤ log (q : ℝ) := Real.log_natCast_nonneg q
    by_cases h2 : 11 / 10 ≤ u.re
    · have a := norm_logDeriv_LFunction_le_vonMangoldt_tsum χ (by linarith : 1 < u.re)
      have b := vonMangoldt_tsum_le_of_eleven_tenths_le u.re h2
      have ha : (fun s => DirichletCharacter.LFunction χ s) = DirichletCharacter.LFunction χ :=
        rfl
      rw [ha]
      linarith
    · exact border_nonprincipal_logDeriv_le_near_one q χ hχ hχ1 u hu h1 (not_le.mp h2).le

end LeanLab.HelfgottMajor.SplitStripCount
