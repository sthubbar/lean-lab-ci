import LeanLab.HelfgottMajor.SPLIT_border_principal_logDeriv_le_near_one

/-!
# Split of `norm_LFunctionTrivChar₁_one_ge_near_one` (`HelfgottMajor/SPLIT_border_principal_logDeriv_le_near_one`)

The target bounds `‖g(u)‖` below by `1/2` for `g(s) = (s - 1) ζ(s)`, Mathlib's
`LFunctionTrivChar₁ 1`, on the two short pieces `1 ≤ Re u ≤ 6/5`, `Im u = ± 3/2`.

The cut is the first order Euler Maclaurin formula at `N = 10`, Titchmarsh, The Theory of the
Riemann Zeta Function, section 2.1, the partial summation behind display 2.1.5 with lower limit `N` in place of `1`:
`ζ(s) = ∑_{n ≤ N} n^{-s} + N^{1-s}/(s - 1) - s ∫_N^∞ {x} x^{-s-1} dx` on `Re s > 0`, `s ≠ 1`.
Multiplied by `s - 1` it splits `g(u)` into the main part
`(u - 1) ∑_{n ≤ 10} n^{-u} + 10^{1-u}` and the error `u (u - 1) ∫_10^∞ {x} x^{-u-1} dx`.

* `riemannZeta_eq_euler_maclaurin`: the formula, a leaf, MEDIUM;
* `norm_integral_fract_le`: `‖∫_N^∞ {x} x^{-s-1} dx‖ ≤ N^{-σ}/σ`, a leaf, EASY, since
  `0 ≤ {x} < 1`;
* `norm_main_part_ge`: the main part has norm at least `1` on the pieces, a leaf, MEDIUM, a
  finite computation; mpmath on 401 points per piece gives the minimum `1.1479`.

Proved here: `‖u‖ ‖u - 1‖ ≤ 3` on the pieces and `10^{-σ}/σ ≤ 1/10` on `σ ≥ 1`, so the error is
at most `3/10`, and `1 - 3/10 ≥ 1/2`.  The twin `norm_LFunctionTrivChar₁_one_ge_near_one_of_leaves`
proves the target statement verbatim from the three leaves.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitPrincipalLowerEM

open Real Complex MeasureTheory

/-- LEAF: the first order Euler Maclaurin formula for `ζ`, Titchmarsh, The Theory of the Riemann
Zeta Function, section 2.1, the derivation of display 2.1.5 with lower limit `N` in place of `1`, valid on `Re s > 0`, `s ≠ 1`, for every
`N ≥ 1`; proved on `Re s > 1` by partial summation and extended by analytic continuation.
MEDIUM. -/
theorem riemannZeta_eq_euler_maclaurin (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = (∑ n ∈ Finset.Icc (1 : ℕ) N, 1 / (n : ℂ) ^ s) + (N : ℂ) ^ (1 - s) / (s - 1) -
      s * ∫ x in Set.Ioi (N : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  sorry

/-- LEAF: the tail integral of the Euler Maclaurin formula is at most `N^{-σ}/σ` in norm, since
`0 ≤ {x} < 1` and `∫_N^∞ x^{-σ-1} dx = N^{-σ}/σ`, Titchmarsh section 2.1.  EASY. -/
theorem norm_integral_fract_le (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ x in Set.Ioi (N : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤
      (N : ℝ) ^ (-s.re) / s.re := by
  sorry

/-- LEAF: the main part `(u - 1) ∑_{n ≤ 10} n^{-u} + 10^{1-u}` of `(u - 1) ζ(u)` has norm at least
`1` on the two pieces `1 ≤ Re u ≤ 6/5`, `Im u = ± 3/2`; a finite computation with ten terms,
by interval arithmetic on the segments.  mpmath gives the minimum `1.1479`.  MEDIUM. -/
theorem norm_main_part_ge (u : ℂ) (h1 : 1 ≤ u.re) (h2 : u.re ≤ 6 / 5)
    (him : u.im = 3 / 2 ∨ u.im = -(3 / 2)) :
    1 ≤ ‖(u - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ u) + (10 : ℂ) ^ (1 - u)‖ := by
  sorry

/-- `‖u‖ ‖u - 1‖ ≤ 3` on the two pieces.  Proved. -/
theorem norm_mul_norm_sub_one_le (u : ℂ) (h1 : 1 ≤ u.re) (h2 : u.re ≤ 6 / 5)
    (him : u.im = 3 / 2 ∨ u.im = -(3 / 2)) : ‖u‖ * ‖u - 1‖ ≤ 3 := by
  have hsq : u.im ^ 2 = 9 / 4 := by rcases him with h | h <;> rw [h] <;> norm_num
  have ha : ‖u‖ ^ 2 ≤ 37 / 10 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  have hb : ‖u - 1‖ ^ 2 ≤ 23 / 10 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]; nlinarith
  have hp : (‖u‖ * ‖u - 1‖) ^ 2 ≤ 9 := by
    rw [mul_pow]
    calc ‖u‖ ^ 2 * ‖u - 1‖ ^ 2 ≤ 37 / 10 * (23 / 10) :=
          mul_le_mul ha hb (sq_nonneg _) (by norm_num)
      _ ≤ 9 := by norm_num
  nlinarith [norm_nonneg u, norm_nonneg (u - 1), mul_nonneg (norm_nonneg u) (norm_nonneg (u - 1))]

/-- `10^{-σ}/σ ≤ 1/10` on `σ ≥ 1`.  Proved. -/
theorem ten_rpow_neg_div_le {σ : ℝ} (hσ : 1 ≤ σ) : (10 : ℝ) ^ (-σ) / σ ≤ 1 / 10 := by
  have h1 : (10 : ℝ) ^ (-σ) ≤ (10 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (10 : ℝ) ^ (-1 : ℝ) = 1 / 10 := by rw [Real.rpow_neg_one]; norm_num
  have hpos : 0 ≤ (10 : ℝ) ^ (-σ) := by positivity
  rw [div_le_iff₀ (by linarith)]
  rw [h2] at h1
  linarith

/-- The target `SplitPrincipalNearOne.norm_LFunctionTrivChar₁_one_ge_near_one`, verbatim, from
the three leaves: `‖g(u)‖ ≥ 1 - 3 · (1/10) ≥ 1/2`. -/
theorem norm_LFunctionTrivChar₁_one_ge_near_one_of_leaves (u : ℂ) (h1 : 1 ≤ u.re)
    (h2 : u.re ≤ 6 / 5) (him : u.im = 3 / 2 ∨ u.im = -(3 / 2)) :
    (1 / 2 : ℝ) ≤ ‖DirichletCharacter.LFunctionTrivChar₁ 1 u‖ := by
  have hu1 : u ≠ 1 := by
    intro h; rw [h] at him; norm_num at him
  have hv : DirichletCharacter.LFunctionTrivChar₁ 1 u =
      (u - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) u :=
    Function.update_of_ne hu1 _ _
  rw [hv, DirichletCharacter.LFunction_modOne_eq,
    riemannZeta_eq_euler_maclaurin 10 (by norm_num) (by linarith) hu1]
  set I := ∫ x in Set.Ioi ((10 : ℕ) : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-u - 1) with hI
  have hsub : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have hexp : (u - 1) * ((∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ u) +
      ((10 : ℕ) : ℂ) ^ (1 - u) / (u - 1) - u * I) =
      ((u - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ u) + (10 : ℂ) ^ (1 - u)) -
        (u * (u - 1)) * I := by
    push_cast
    field_simp
  rw [hexp]
  have hM := norm_main_part_ge u h1 h2 him
  have hE : ‖(u * (u - 1)) * I‖ ≤ 3 / 10 := by
    rw [norm_mul, norm_mul]
    have a := norm_mul_norm_sub_one_le u h1 h2 him
    have b := norm_integral_fract_le 10 (by norm_num) (s := u) (by linarith)
    have c := ten_rpow_neg_div_le h1
    push_cast at b
    have hIb : ‖I‖ ≤ 1 / 10 := b.trans c
    calc ‖u‖ * ‖u - 1‖ * ‖I‖ ≤ 3 * (1 / 10) :=
          mul_le_mul a hIb (norm_nonneg _) (by norm_num)
      _ = 3 / 10 := by norm_num
  have := norm_sub_norm_le ((u - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ u) +
    (10 : ℂ) ^ (1 - u)) ((u * (u - 1)) * I)
  linarith

end LeanLab.HelfgottMajor.SplitPrincipalLowerEM
