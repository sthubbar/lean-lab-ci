import LeanLab.HelfgottMajor.SPLIT_principal_contour_identity
import LeanLab.Linnik.ExplicitFormula.LeftHalf

/-!
Split of `principal_contour_shift_two_to_minus_half` in
`SPLIT_principal_contour_identity.lean`.

The single identity of the target moves the vertical line of the logarithmic derivative of
the Dirichlet `L`-function from real part two down to real part minus one half, at
conductor one, and it is cut here along the three steps that the move consists of:

1. on the line of real part two the logarithmic derivative is the Dirichlet series of the
   weighted von Mangoldt sum, so the vertical integral on that line is minus the twisted
   prime sum; no contour moves in this step;
2. the move itself, the contour shift of Lemma 4.1 at page 33 display 4.7: it crosses the
   pole at one, whose residue is the conductor one main term, every nontrivial zero of the
   strip, which gives the two zero sums split at the height `T`, and the pole at zero,
   whose residue is log of two pi;
3. at conductor one the character is the trivial one and its `L`-function is the Riemann
   zeta function, so the vertical integral on the line of real part minus one half is the
   principal contour.

A fourth leaf records that the integrand on the line of real part minus one half is
integrable, which is what makes that line an available contour at all; the target asserts
a value for that integral and cannot do so without it.

The integrability leaf is proved from the left line bound for the logarithmic derivative of the
`L`-function that `LeanLab.Linnik.ExplicitFormula.LeftHalf` establishes for primitive characters,
together with the primitive factorisation of the `L`-function that Mathlib gives in
`LFunction_changeLevel`.  That file and its whole closure are sorry free, and this is the one
import this file adds.

On the repair pass the first and the third of those identities are proved from the theorems
`principal_prime_sum_mellin_contour` and `principal_contour_conductor_one` of the imported
file, of which they are restatements, so only the shift itself and the integrability of the
line of real part minus one half stay open.

The assembly at the end chains the three identities, and its own argument is a rewrite and
`ring` only.  It does not use the target theorem, and it does not use the assembly of the
imported split file, which carries the target as an input.

Degenerate values.  The scale hypothesis is only `1 ≤ x`, so no negative and no zero scale
occurs, every power `(x : ℂ) ^ s` is taken at positive base, and at `x = 1` the scale
factor is `1` unless the exponent is `0`.  Every contour below is an integral over all of
`ℝ` on a line at real part two or at real part minus one half; on the second line the
continued Gaussian transform divides by the contour parameter `-1 / 2 + t * I`, whose real
part is `-1 / 2`, so that divisor is never zero and the transform has no junk value there.
The only other division is the fixed factor `1 / (2 * π)`, and `2 * π` is not zero.  The
branching term `if q = 1` is kept verbatim, so it is the main term at `q = 1` and zero
otherwise, and the hypothesis `hq : q = 1` makes the branch taken, never an unsatisfiable
combination.  At `δ = 0` the shift factor `2 * π * I * δ` of the continued transform is
zero and the transformation is the plain Gaussian; nothing in the leaves degenerates there.
The height `T` is unconstrained, and the two zero sets `<|im| ≤ T` and `T < |im|` split the
zeros of the strip for every real `T`, including `T = 0` and negative `T`, where the first
of them is empty and the sum over it is zero.
-/

namespace LeanLab.HelfgottMajor.SPLIT_principal_contour_identity
open Real MeasureTheory LeanLab.HelfgottArcs Decomp123 Decomp269a Contour457

open scoped ArithmeticFunction

/-! ### A. The line of real part two is the prime sum -/

/-- LEAF. Step one, the line of real part two.  The vertical integral at real part two of
the logarithmic derivative of the `L`-function against the shifted Gaussian transform and
the scale factor is minus the twisted von Mangoldt sum.  The line lies in the half plane of
absolute convergence, no zero of the `L`-function lies on it, and this step moves no
contour: it only writes the prime sum as an integral.  It says nothing about the line of
real part minus one half, about log of two pi, or about either zero sum.  It is the
negation of `principal_prime_sum_mellin_contour` of the imported file, which is already
proved there, and the repair pass takes it from that theorem. -/
theorem principal_two_line_prime_sum (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) = - Schi etaHeart χ δ x := by
  rw [principal_prime_sum_mellin_contour x hx q χ δ]
  ring

/-! ### B. The move from real part two to real part minus one half -/

/-- LEAF. Step two, the contour shift at conductor one, Lemma 4.1 at page 33 display 4.7.
The weighted von Mangoldt sum equals minus the principal contour minus log of two pi, plus
the guarded conductor one main term, minus the two zero sums split at the height `T`. It is
one leg: the line of real part one half is no contour, since the logarithmic derivative is
not integrable across the zeros of that line. It asserts no size estimate for the contour
and no bound for either zero sum, and it needs no hypothesis on the location of the zeros. -/
theorem principal_explicit_formula_shift (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hq : q = 1) :
    Schi etaHeart χ δ x =
      -((log (2 * π) : ℂ)) - principalContour δ x +
        (if q = 1 then fhat etaHeart (-δ) * x else 0) -
        lowZeros χ δ x T - highZeros χ δ x T := by
  sorry

/-! ### C. The line of real part minus one half at conductor one -/

/-- LEAF. Step three, the conductor one identification.  At conductor one the character is
the trivial one and its `L`-function is the Riemann zeta function, so the vertical integral
at real part minus one half of the logarithmic derivative against the continued Gaussian
transform and the scale factor is literally the principal contour of the target.  This is a
naming step: no contour moves and no sum occurs.  It is the theorem
`principal_contour_conductor_one` of the imported file restated with the binders in the
order this assembly uses, and the repair pass takes it from that theorem. -/
theorem principal_half_line_conductor_one (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) (hq : q = 1) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) = principalContour δ x := by
  exact principal_contour_conductor_one x hx q χ hq δ


/-! #### A0. The Gaussian Mellin transform decays on every vertical line of real part at
least one half -/

/-- A uniform bound for the Gaussian Mellin transform on a fixed vertical line. -/
private theorem pcst_mellin_line_constant (δ σ : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ‖gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ B := by
  refine ⟨(∫ x in Set.Ioi (0 : ℝ), x ^ (σ - 1) * exp (-x ^ 2 / 2)) + 1, ?_, ?_⟩
  · have h0 : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), x ^ (σ - 1) * exp (-x ^ 2 / 2) :=
      setIntegral_nonneg measurableSet_Ioi fun x hx =>
        mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
    linarith
  · intro t
    have h := Gaussian269.mellin_norm_le δ ((σ : ℂ) + t * Complex.I)
    have hre : ((σ : ℂ) + t * Complex.I).re = σ := by simp
    rw [hre] at h
    linarith

/-- One recurrence step for the Gaussian Mellin transform, in norm form. -/
private theorem pcst_mellin_step (δ : ℝ) (u : ℂ) (hu : 0 < u.re) :
    ‖gaussianMellin δ u‖ * ‖u‖ ≤
      ‖gaussianMellin δ (u + 2)‖ +
        ‖(2 * π * Complex.I * δ : ℂ)‖ * ‖gaussianMellin δ (u + 1)‖ := by
  have h := Continuation457.gaussian_mellin_recurrence δ u hu
  calc ‖gaussianMellin δ u‖ * ‖u‖ = ‖u * gaussianMellin δ u‖ := by rw [norm_mul, mul_comm]
    _ = ‖gaussianMellin δ (u + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (u + 1)‖ := by
        rw [h]
    _ ≤ ‖gaussianMellin δ (u + 2)‖ +
          ‖(2 * π * Complex.I * δ) * gaussianMellin δ (u + 1)‖ := norm_sub_le _ _
    _ = ‖gaussianMellin δ (u + 2)‖ +
          ‖(2 * π * Complex.I * δ : ℂ)‖ * ‖gaussianMellin δ (u + 1)‖ := by rw [norm_mul]

/-- Three recurrence steps give quadratic decay of the Gaussian Mellin transform on every
vertical line of real part at least one half. -/
private theorem pcst_mellin_decay_half (δ σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
  obtain ⟨B2, hB2, hB2'⟩ := pcst_mellin_line_constant δ (σ + 2)
  obtain ⟨B3, hB3, hB3'⟩ := pcst_mellin_line_constant δ (σ + 3)
  obtain ⟨B4, hB4, hB4'⟩ := pcst_mellin_line_constant δ (σ + 4)
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  have hP : 0 ≤ B4 + c * B3 + c * (B3 + c * B2) := by
    have h1 : 0 ≤ c * B3 := mul_nonneg hc0 hB3.le
    have h2 : 0 ≤ c * (B3 + c * B2) :=
      mul_nonneg hc0 (by have := mul_nonneg hc0 hB2.le; linarith)
    linarith
  refine ⟨4 * (B4 + c * B3 + c * (B3 + c * B2)) + 1, by linarith, fun t => ?_⟩
  set a : ℂ := (σ : ℂ) + t * Complex.I with ha
  have hare : a.re = σ := by rw [ha]; simp
  have ha2 : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h1 : a.re = σ := hare
    have h2 : a.im = t := by rw [ha]; simp
    rw [h1, h2]
    nlinarith
  have hb2 : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a + 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h1 : (a + 1).re = σ + 1 := by rw [ha]; simp
    have h2 : (a + 1).im = t := by rw [ha]; simp
    rw [h1, h2]
    nlinarith
  have hquarter : (0 : ℝ) < (1 / 4 : ℝ) + t ^ 2 := by positivity
  have hapos : 0 < ‖a‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : a.re = 0 := by rw [h]; simp
    rw [hare] at h1
    linarith
  have hbpos : 0 < ‖a + 1‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : (a + 1).re = 0 := by rw [h]; simp
    have h2 : (a + 1).re = σ + 1 := by rw [ha]; simp
    rw [h2] at h1
    linarith
  have ha1 : 0 < (a + 1).re := by rw [ha]; simp; linarith
  have ha2' : 0 < (a + 2).re := by rw [ha]; simp; linarith
  have hstep1 := pcst_mellin_step δ a (by rw [hare]; linarith)
  have hstep2 := pcst_mellin_step δ (a + 1) ha1
  have hstep3 := pcst_mellin_step δ (a + 2) ha2'
  have e2 : a + 2 = ((σ + 2 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have e3 : a + 3 = ((σ + 3 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have e4 : a + 4 = ((σ + 4 : ℝ) : ℂ) + t * Complex.I := by rw [ha]; push_cast; ring
  have h3 : ‖gaussianMellin δ (a + 2)‖ * ‖a + 2‖ ≤ B4 + c * B3 := by
    have hb : ‖gaussianMellin δ ((a + 2) + 2)‖ ≤ B4 := by
      rw [show (a + 2) + 2 = a + 4 by ring, e4]; exact hB4' t
    have hc1 : ‖gaussianMellin δ ((a + 2) + 1)‖ ≤ B3 := by
      rw [show (a + 2) + 1 = a + 3 by ring, e3]; exact hB3' t
    calc ‖gaussianMellin δ (a + 2)‖ * ‖a + 2‖
        ≤ ‖gaussianMellin δ ((a + 2) + 2)‖ + c * ‖gaussianMellin δ ((a + 2) + 1)‖ := hstep3
      _ ≤ B4 + c * B3 := by
          refine add_le_add hb (mul_le_mul_of_nonneg_left hc1 hc0)
  have h2 : ‖gaussianMellin δ (a + 1)‖ * ‖a + 1‖ ≤ B3 + c * B2 := by
    have hb : ‖gaussianMellin δ ((a + 1) + 2)‖ ≤ B3 := by
      rw [show (a + 1) + 2 = a + 3 by ring, e3]; exact hB3' t
    have hc1 : ‖gaussianMellin δ ((a + 1) + 1)‖ ≤ B2 := by
      rw [show (a + 1) + 1 = a + 2 by ring, e2]; exact hB2' t
    calc ‖gaussianMellin δ (a + 1)‖ * ‖a + 1‖
        ≤ ‖gaussianMellin δ ((a + 1) + 2)‖ + c * ‖gaussianMellin δ ((a + 1) + 1)‖ := hstep2
      _ ≤ B3 + c * B2 := by
          refine add_le_add hb (mul_le_mul_of_nonneg_left hc1 hc0)
  have h2pos : 0 < ‖a + 2‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : (a + 2).re = 0 := by rw [h]; simp
    linarith
  have hquot2 : ‖gaussianMellin δ (a + 2)‖ ≤ (B4 + c * B3) / ‖a + 2‖ := by
    rw [le_div_iff₀ h2pos]
    linarith [h3]
  have hquot1 : ‖gaussianMellin δ (a + 1)‖ ≤ (B3 + c * B2) / ‖a + 1‖ := by
    rw [le_div_iff₀ hbpos]
    linarith [h2]
  have hle : ‖a + 1‖ ≤ ‖a + 2‖ := by
    have hn1 : Complex.normSq (a + 1) = (σ + 1) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply]
      have h1 : (a + 1).re = σ + 1 := by rw [ha]; simp
      have h2 : (a + 1).im = t := by rw [ha]; simp
      rw [h1, h2]; ring
    have hn2 : Complex.normSq (a + 2) = (σ + 2) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply]
      have h1 : (a + 2).re = σ + 2 := by rw [ha]; simp
      have h2 : (a + 2).im = t := by rw [ha]; simp
      rw [h1, h2]; ring
    rw [show ‖a + 1‖ = Real.sqrt (Complex.normSq (a + 1)) by
          rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)],
      show ‖a + 2‖ = Real.sqrt (Complex.normSq (a + 2)) by
          rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]
    apply Real.sqrt_le_sqrt
    rw [hn1, hn2]
    nlinarith
  have hsum : ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖ ≤
      B4 + c * B3 + c * (B3 + c * B2) := by
    have hb1 : (B4 + c * B3) / ‖a + 2‖ ≤ (B4 + c * B3) / ‖a + 1‖ := by
      have hnum : (0 : ℝ) ≤ B4 + c * B3 := by
        have := mul_nonneg hc0 hB3.le; linarith [hB4.le]
      exact div_le_div_of_nonneg_left hnum hbpos hle
    have hmid : ‖gaussianMellin δ a‖ * ‖a‖ ≤
        (B4 + c * B3 + c * (B3 + c * B2)) / ‖a + 1‖ := by
      have hb2' : c * ((B3 + c * B2) / ‖a + 1‖) = c * (B3 + c * B2) / ‖a + 1‖ := by ring
      calc ‖gaussianMellin δ a‖ * ‖a‖
          ≤ ‖gaussianMellin δ (a + 2)‖ + c * ‖gaussianMellin δ (a + 1)‖ := hstep1
        _ ≤ (B4 + c * B3) / ‖a + 2‖ + c * ((B3 + c * B2) / ‖a + 1‖) := by
            refine add_le_add hquot2 (mul_le_mul_of_nonneg_left hquot1 hc0)
        _ ≤ (B4 + c * B3) / ‖a + 1‖ + c * (B3 + c * B2) / ‖a + 1‖ := by
            rw [hb2']
            exact add_le_add hb1 le_rfl
        _ = (B4 + c * B3 + c * (B3 + c * B2)) / ‖a + 1‖ := by ring
    calc ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖
        ≤ ((B4 + c * B3 + c * (B3 + c * B2)) / ‖a + 1‖) * ‖a + 1‖ :=
          mul_le_mul_of_nonneg_right hmid hbpos.le
      _ = B4 + c * B3 + c * (B3 + c * B2) := by field_simp
  have hmain : ‖gaussianMellin δ a‖ ≤
      (B4 + c * B3 + c * (B3 + c * B2)) / (‖a‖ * ‖a + 1‖) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖a‖ * ‖a + 1‖)]
    calc ‖gaussianMellin δ a‖ * (‖a‖ * ‖a + 1‖) =
        ‖gaussianMellin δ a‖ * ‖a‖ * ‖a + 1‖ := by ring
      _ ≤ _ := hsum
  have hden : (1 / 4 : ℝ) + t ^ 2 ≤ ‖a‖ * ‖a + 1‖ := by
    have h1 : 0 ≤ ‖a‖ := norm_nonneg _
    have h2 : 0 ≤ ‖a + 1‖ := norm_nonneg _
    nlinarith [ha2, hb2]
  have hfin : ‖gaussianMellin δ a‖ ≤
      (B4 + c * B3 + c * (B3 + c * B2)) / ((1 / 4 : ℝ) + t ^ 2) :=
    hmain.trans (div_le_div_of_nonneg_left hP hquarter hden)
  have hfour : (B4 + c * B3 + c * (B3 + c * B2)) / ((1 / 4 : ℝ) + t ^ 2) ≤
      (4 * (B4 + c * B3 + c * (B3 + c * B2)) + 1) / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ hquarter (by positivity : (0 : ℝ) < 1 + t ^ 2)]
    nlinarith [hP]
  simpa [ha] using hfin.trans hfour

/-- The continued Gaussian transform decays quadratically on the line of real part minus one
half. -/
private theorem pcst_continuedGaussian_decay (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨K1, hK1, hK1'⟩ := pcst_mellin_decay_half δ (1 / 2) le_rfl
  obtain ⟨K2, hK2, hK2'⟩ := pcst_mellin_decay_half δ (3 / 2) (by norm_num)
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  have hP : 0 ≤ K2 + c * K1 := by
    have h := mul_nonneg hc0 hK1.le
    linarith [hK2.le]
  refine ⟨2 * (K2 + c * K1) + 1, by linarith, fun t => ?_⟩
  set s : ℂ := (-1 / 2 : ℂ) + t * Complex.I with hs
  have hsre : s.re = -1 / 2 := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hsq : ‖s‖ ^ 2 = (1 / 4 : ℝ) + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hsre, hsim]
    ring
  have h2 : (1 / 2 : ℝ) ≤ ‖s‖ := by
    have h0 : 0 ≤ ‖s‖ := norm_nonneg _
    nlinarith [sq_nonneg t]
  have hun : continuedGaussian δ s =
      (gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)) / s :=
    rfl
  have e1 : s + 1 = ((1 / 2 : ℝ) : ℂ) + t * Complex.I := by rw [hs]; push_cast; ring
  have e2 : s + 2 = ((3 / 2 : ℝ) : ℂ) + t * Complex.I := by rw [hs]; push_cast; ring
  have hden1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hb1 : ‖gaussianMellin δ (s + 1)‖ ≤ K1 / (1 + t ^ 2) := by rw [e1]; exact hK1' t
  have hb2v : ‖gaussianMellin δ (s + 2)‖ ≤ K2 / (1 + t ^ 2) := by rw [e2]; exact hK2' t
  have hnum : ‖gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ ≤
      (K2 + c * K1) / (1 + t ^ 2) := by
    calc ‖gaussianMellin δ (s + 2) - (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖
        ≤ ‖gaussianMellin δ (s + 2)‖ +
            ‖(2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ := norm_sub_le _ _
      _ = ‖gaussianMellin δ (s + 2)‖ + c * ‖gaussianMellin δ (s + 1)‖ := by rw [norm_mul, hc]
      _ ≤ K2 / (1 + t ^ 2) + c * (K1 / (1 + t ^ 2)) := by
          refine add_le_add hb2v (mul_le_mul_of_nonneg_left hb1 hc0)
      _ = (K2 + c * K1) / (1 + t ^ 2) := by ring
  have hmul : ‖continuedGaussian δ s‖ ≤ ((K2 + c * K1) / (1 + t ^ 2)) / (1 / 2) := by
    rw [hun, norm_div]
    have hstep1 : ‖gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ / ‖s‖ ≤
        ‖gaussianMellin δ (s + 2) -
          (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) h2
    have hstep2 : ‖gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ / (1 / 2) ≤
        ((K2 + c * K1) / (1 + t ^ 2)) / (1 / 2) :=
      div_le_div_of_nonneg_right hnum (by norm_num)
    exact hstep1.trans hstep2
  have hfin : ((K2 + c * K1) / (1 + t ^ 2)) / (1 / 2) ≤
      (2 * (K2 + c * K1) + 1) / (1 + t ^ 2) := by
    have he : ((K2 + c * K1) / (1 + t ^ 2)) / (1 / 2) =
        2 * (K2 + c * K1) / (1 + t ^ 2) := by field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ hden1.le
    linarith
  simpa [hs] using hmul.trans hfin

/-! #### A1. The logarithmic derivative of the L-function on the line of real part minus
one half, for every Dirichlet character -/

/-- The cast of a natural number to the complexes, through the reals. -/
private theorem pcst_natCast_eq_ofReal (b : ℕ) : ((b : ℂ)) = ((b : ℝ) : ℂ) := by
  push_cast
  ring

/-- A Dirichlet character has unit modulus on units. -/
private theorem pcst_norm_apply_eq_one {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {a : ZMod d} (ha : IsUnit a) : ‖χ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have hmul : ‖χ (u : ZMod d)‖ * ‖χ (((u⁻¹ : (ZMod d)ˣ) : ZMod d))‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h1 := DirichletCharacter.norm_le_one (χ := χ) (((u⁻¹ : (ZMod d)ˣ) : ZMod d))
  have h2 := DirichletCharacter.norm_le_one (χ := χ) (u : ZMod d)
  nlinarith [norm_nonneg (χ (u : ZMod d)),
    norm_nonneg (χ (((u⁻¹ : (ZMod d)ˣ) : ZMod d)))]

/-- The L-function of a Dirichlet character is analytic away from one. -/
private theorem pcst_analyticAt_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) :=
    fun z hz =>
      (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  exact hdiff.analyticOnNhd isOpen_compl_singleton s (by simpa using hs)

/-- The primitive factorisation of the L-function: a character is a primitive one times a
finite Euler product over the primes of its level. -/
private theorem pcst_LFunction_factorization {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero (DirichletCharacter.conductor χ)] {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.LFunction χ.primitiveCharacter s *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-s)) := by
  have h := DirichletCharacter.LFunction_changeLevel (M := DirichletCharacter.conductor χ)
    (N := q) (DirichletCharacter.conductor_dvd_level χ) (χ := χ.primitiveCharacter) (Or.inr hs)
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  simpa only [pcst_natCast_eq_ofReal] using h

/-- No Euler factor vanishes on the line of real part minus one half. -/
private theorem pcst_prime_factor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero (DirichletCharacter.conductor χ)]
    (p : ℕ) (hp : p ∈ q.primeFactors) {s : ℂ} (hre : s.re = -1 / 2) :
    1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
      ((p : ℝ) : ℂ) ^ (-s) ≠ 0 := by
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnorm : ‖((p : ℝ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have hre' : (-s).re = 1 / 2 := by
      rw [Complex.neg_re, hre]
      norm_num
    rw [hre']
  have hsqrt : (1 : ℝ) < (p : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) < (p : ℝ))
      (by norm_num : (0 : ℝ) < 1 / 2)
    rwa [Real.one_rpow] at h1
  rintro h
  have hz : χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
      ((p : ℝ) : ℂ) ^ (-s) = 1 := by
    linear_combination -h
  rcases eq_or_ne (χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ))) 0 with hc | hc
  · rw [hc, zero_mul] at hz
    exact zero_ne_one hz
  · have hunit : IsUnit (p : ZMod (DirichletCharacter.conductor χ)) := by
      by_contra hnu
      exact hc (MulChar.map_nonunit χ.primitiveCharacter hnu)
    have hc1 : ‖χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ))‖ = 1 :=
      pcst_norm_apply_eq_one χ.primitiveCharacter hunit
    have h2 := congrArg norm hz
    rw [norm_one, norm_mul, hc1, hnorm, one_mul] at h2
    linarith

/-- `z ↦ b ^ (-z)` differentiates to `-log b * b ^ (-z)`. -/
private theorem pcst_hasDerivAt_cpow_neg (b : ℝ) (hb : 0 < b) (w : ℂ) :
    HasDerivAt (fun z : ℂ => ((b : ℝ) : ℂ) ^ (-z))
      (-(Real.log b : ℂ) * ((b : ℝ) : ℂ) ^ (-w)) w := by
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have heq : ∀ z : ℂ, Complex.exp (Complex.log ((b : ℝ) : ℂ) * (-z)) =
      ((b : ℝ) : ℂ) ^ (-z) := by
    intro z
    rw [Complex.cpow_def_of_ne_zero hbC]
  have hinner : HasDerivAt (fun z : ℂ => Complex.log ((b : ℝ) : ℂ) * (-z))
      (Complex.log ((b : ℝ) : ℂ) * (-1)) w := by
    simpa using (hasDerivAt_id w).neg.const_mul (Complex.log ((b : ℝ) : ℂ))
  have hexp := hinner.cexp
  rw [show (fun z : ℂ => Complex.exp (Complex.log ((b : ℝ) : ℂ) * (-z)))
      = fun z : ℂ => ((b : ℝ) : ℂ) ^ (-z) from funext heq] at hexp
  refine hexp.congr_deriv ?_
  rw [← heq w, ← Complex.ofReal_log hb.le]
  ring

/-- The logarithmic derivative of one Euler factor. -/
private theorem pcst_factor_logDeriv (b : ℝ) (hb : 0 < b) (c : ℂ) (s : ℂ) :
    logDeriv (fun z : ℂ => 1 - c * ((b : ℝ) : ℂ) ^ (-z)) s =
      c * (Real.log b : ℂ) * ((b : ℝ) : ℂ) ^ (-s) / (1 - c * ((b : ℝ) : ℂ) ^ (-s)) := by
  have hd : HasDerivAt (fun z : ℂ => 1 - c * ((b : ℝ) : ℂ) ^ (-z))
      (-(c * (-(Real.log b : ℂ) * ((b : ℝ) : ℂ) ^ (-s)))) s := by
    have h1 : HasDerivAt (fun z : ℂ => c * ((b : ℝ) : ℂ) ^ (-z))
        (c * (-(Real.log b : ℂ) * ((b : ℝ) : ℂ) ^ (-s))) s :=
      (pcst_hasDerivAt_cpow_neg b hb s).const_mul c
    have h0 : HasDerivAt (fun _ : ℂ => (1 : ℂ)) (0 : ℂ) s := hasDerivAt_const s 1
    have hsub := h0.sub h1
    have hfun : ((fun _ : ℂ => (1 : ℂ)) - fun z : ℂ => c * ((b : ℝ) : ℂ) ^ (-z))
        = fun z : ℂ => 1 - c * ((b : ℝ) : ℂ) ^ (-z) := by
      funext z
      simp
    rw [hfun] at hsub
    convert hsub using 1
    ring
  rw [logDeriv_apply, hd.deriv]
  ring

/-- The logarithmic derivative of one Euler factor is at most four logarithms in size on the
line of real part minus one half. -/
private theorem pcst_factor_logDeriv_bound {d : ℕ} [NeZero d] (χ₀ : DirichletCharacter ℂ d)
    (p : ℕ) (hp : 2 ≤ p) {s : ℂ} (hre : s.re = -1 / 2) :
    ‖logDeriv (fun z : ℂ => 1 - χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-z)) s‖ ≤
      4 * Real.log p := by
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hplog : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hnorm : ‖((p : ℝ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have hre' : (-s).re = 1 / 2 := by
      rw [Complex.neg_re, hre]
      norm_num
    rw [hre']
  rw [pcst_factor_logDeriv (p : ℝ) hp0 (χ₀ (p : ZMod d)) s]
  rcases eq_or_ne (χ₀ (p : ZMod d)) 0 with hc | hc
  · rw [hc]
    simp only [zero_mul, norm_div, norm_zero, zero_div, norm_mul]
    positivity
  · have hunit : IsUnit (p : ZMod d) := by
      by_contra hnu
      exact hc (MulChar.map_nonunit χ₀ hnu)
    have hc1 : ‖χ₀ (p : ZMod d)‖ = 1 := pcst_norm_apply_eq_one χ₀ hunit
    have hznorm : ‖χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (1 / 2 : ℝ) := by
      rw [norm_mul, hc1, hnorm, one_mul]
    have hden : (p : ℝ) ^ (1 / 2 : ℝ) - 1 ≤
        ‖1 - χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ := by
      have h := abs_norm_sub_norm_le (χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)) (1 : ℂ)
      rw [norm_one, norm_sub_rev] at h
      have h2 := le_abs_self (‖χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ - 1)
      linarith
    have hsqrt : (4 / 3 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
      have h2 : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (by linarith)
      have h0 : (0 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
      have hrw : (p : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (p : ℝ) :=
        (Real.sqrt_eq_rpow (p : ℝ)).symm
      rw [hrw]
      nlinarith [h2, h0, hp2R]
    have hdenpos : 0 < (p : ℝ) ^ (1 / 2 : ℝ) - 1 := by linarith
    have hnum : ‖χ₀ (p : ZMod d) * (Real.log (p : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ (-s)‖ =
        (p : ℝ) ^ (1 / 2 : ℝ) * Real.log (p : ℝ) := by
      rw [norm_mul, norm_mul, hc1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hplog.le,
        hnorm, one_mul]
      ring
    rw [norm_div, hnum]
    have hpos : (0 : ℝ) < ‖1 - χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ :=
      lt_of_lt_of_le hdenpos hden
    have hstep : (p : ℝ) ^ (1 / 2 : ℝ) * Real.log (p : ℝ) /
        ‖1 - χ₀ (p : ZMod d) * ((p : ℝ) : ℂ) ^ (-s)‖ ≤
        (p : ℝ) ^ (1 / 2 : ℝ) * Real.log (p : ℝ) / ((p : ℝ) ^ (1 / 2 : ℝ) - 1) :=
      div_le_div_of_nonneg_left (by positivity) hdenpos hden
    have hfin : (p : ℝ) ^ (1 / 2 : ℝ) * Real.log (p : ℝ) / ((p : ℝ) ^ (1 / 2 : ℝ) - 1) ≤
        4 * Real.log (p : ℝ) := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [hsqrt, hplog]
    linarith

/-- The left line bound for the logarithmic derivative of the L-function of an arbitrary
Dirichlet character. -/
private theorem pcst_logDeriv_LFunction_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero (DirichletCharacter.conductor χ)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
        C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C₀, hC₀, hL₀⟩ := LeanLab.Linnik.ExplicitFormula.logDeriv_left_line
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C₀ + 4 * (q.primeFactors.card : ℝ) / Real.log 2, by positivity, fun t => ?_⟩
  have hne1 : ((-1 / 2 : ℂ) + t * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    norm_num at hre
  have hre : ((-1 / 2 : ℂ) + t * Complex.I).re = -1 / 2 := by simp
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds ((-1 / 2 : ℂ) + t * Complex.I)]
      fun z : ℂ => DirichletCharacter.LFunction χ.primitiveCharacter z *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)) := by
    filter_upwards [isOpen_ne.mem_nhds hne1] with z hz
    exact pcst_LFunction_factorization χ hz
  have hprod : (fun z : ℂ => ∏ p ∈ q.primeFactors,
        (1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z)))
      = ∏ p ∈ q.primeFactors, (fun z : ℂ =>
          1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)) := by
    funext z
    rw [Finset.prod_apply]
  have hne0 : DirichletCharacter.LFunction χ.primitiveCharacter
      ((-1 / 2 : ℂ) + t * Complex.I) ≠ 0 :=
    LeanLab.Linnik.ExplicitFormula.no_zero_left_line χ.primitiveCharacter_isPrimitive t
  have hneP : (∏ p ∈ q.primeFactors, (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z))) ((-1 / 2 : ℂ) + t * Complex.I) ≠ 0 := by
    rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => pcst_prime_factor_ne_zero χ p hp hre
  have hd0 : DifferentiableAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter)
      ((-1 / 2 : ℂ) + t * Complex.I) :=
    DirichletCharacter.differentiableAt_LFunction χ.primitiveCharacter _ (Or.inl hne1)
  have hdPterm : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ =>
      1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
        ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    exact ((((pcst_hasDerivAt_cpow_neg (p : ℝ) hp0 _).const_mul _)).const_sub 1).differentiableAt
  have hdP : DifferentiableAt ℂ (∏ p ∈ q.primeFactors, (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z))) ((-1 / 2 : ℂ) + t * Complex.I) :=
    DifferentiableAt.finsetProd hdPterm
  have hsplit : logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) =
      logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)
          ((-1 / 2 : ℂ) + t * Complex.I) +
        ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ =>
          1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I) := by
    rw [(logDeriv_congr_nhds hev).eq_of_nhds]
    have hfun2 : (fun z : ℂ => DirichletCharacter.LFunction χ.primitiveCharacter z *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)))
        = DirichletCharacter.LFunction χ.primitiveCharacter *
            ∏ p ∈ q.primeFactors, (fun z : ℂ =>
              1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
                ((p : ℝ) : ℂ) ^ (-z)) := by
      funext z
      rw [Pi.mul_apply, Finset.prod_apply]
    rw [hfun2,
      logDeriv_mul (f := DirichletCharacter.LFunction χ.primitiveCharacter)
        (g := ∏ p ∈ q.primeFactors, (fun z : ℂ =>
          1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)))
        ((-1 / 2 : ℂ) + t * Complex.I) hne0 hneP hd0 hdP,
      logDeriv_prod (fun p hp => pcst_prime_factor_ne_zero χ p hp hre) hdPterm]
  have hb0 : ‖logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)
      ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      C₀ * Real.log ((DirichletCharacter.conductor χ : ℝ) * (|t| + 2)) := by
    rw [logDeriv_apply]
    exact hL₀ (DirichletCharacter.conductor χ) χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive t
  have hbp : ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      4 * (q.primeFactors.card : ℝ) * Real.log q := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hterm : ∀ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ =>
        1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
          ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ 4 * Real.log q := by
      intro p hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have hpdiv : p ∣ q := Nat.dvd_of_mem_primeFactors hp
      have hpq : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hpdiv
      have hpqR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by omega : 0 < p)
      have hlog : Real.log (p : ℝ) ≤ Real.log (q : ℝ) := Real.log_le_log hp0 hpqR
      calc ‖logDeriv (fun z : ℂ =>
            1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
              ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖
          ≤ 4 * Real.log (p : ℝ) := pcst_factor_logDeriv_bound χ.primitiveCharacter p hp2 hre
        _ ≤ 4 * Real.log (q : ℝ) := by linarith
    calc ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ =>
          1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
            ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖
        ≤ ∑ _p ∈ q.primeFactors, 4 * Real.log (q : ℝ) := Finset.sum_le_sum hterm
      _ = 4 * (q.primeFactors.card : ℝ) * Real.log (q : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hLnonneg : 0 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_nonneg
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    nlinarith [abs_nonneg t]
  have hdq_pos : 0 < ((DirichletCharacter.conductor χ : ℕ) : ℝ) := by
    have h : 0 < DirichletCharacter.conductor χ :=
      Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero (χ := χ))
    exact_mod_cast h
  have hqbound : Real.log ((DirichletCharacter.conductor χ : ℝ) * (|t| + 2)) ≤
      Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (by positivity)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hdvd : DirichletCharacter.conductor χ ∣ q := DirichletCharacter.conductor_dvd_level χ
    have hdq : DirichletCharacter.conductor χ ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd
    have hdc : ((DirichletCharacter.conductor χ : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    nlinarith [abs_nonneg t]
  have hlogq : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log
    · have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      linarith
    · have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      nlinarith [abs_nonneg t]
  have hlogq0 : 0 ≤ Real.log (q : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcard0 : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) := by positivity
  have hsumle := norm_sum_le q.primeFactors (fun p : ℕ => logDeriv (fun z : ℂ =>
    1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
      ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I))
  calc ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖
      = ‖logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)
            ((-1 / 2 : ℂ) + t * Complex.I) +
          ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ =>
            1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
              ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ := by rw [hsplit]
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)
            ((-1 / 2 : ℂ) + t * Complex.I)‖ +
          ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ =>
            1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
              ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ := norm_add_le _ _
    _ ≤ C₀ * Real.log ((DirichletCharacter.conductor χ : ℝ) * (|t| + 2)) +
          ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ =>
            1 - χ.primitiveCharacter (p : ZMod (DirichletCharacter.conductor χ)) *
              ((p : ℝ) : ℂ) ^ (-z)) ((-1 / 2 : ℂ) + t * Complex.I)‖ := by
        linarith [hb0, hsumle]
    _ ≤ C₀ * Real.log ((q : ℝ) * (|t| + 2)) + 4 * (q.primeFactors.card : ℝ) * Real.log (q : ℝ) := by
        have h1 : C₀ * Real.log ((DirichletCharacter.conductor χ : ℝ) * (|t| + 2)) ≤
            C₀ * Real.log ((q : ℝ) * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left hqbound hC₀
        linarith [h1, hbp]
    _ ≤ (C₀ + 4 * (q.primeFactors.card : ℝ) / Real.log 2) *
          Real.log ((q : ℝ) * (|t| + 2)) := by
        have key : 4 * (q.primeFactors.card : ℝ) * Real.log (q : ℝ) ≤
            4 * (q.primeFactors.card : ℝ) / Real.log 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
          have hl21 : Real.log 2 ≤ 1 := by
            have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            linarith
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
          have hml : Real.log 2 * Real.log (q : ℝ) ≤ 1 * Real.log ((q : ℝ) * (|t| + 2)) := by
            have h1 := mul_le_mul hl21 hlogq hlogq0 (by norm_num : (0 : ℝ) ≤ 1)
            simpa using h1
          nlinarith [hcard0]
        nlinarith [key]

/-- Continuity of the logarithmic derivative of the L-function on the line of real part minus
one half. -/
private theorem pcst_logDeriv_LFunction_continuous (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero (DirichletCharacter.conductor χ)] :
    Continuous (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hne1 : ((-1 / 2 : ℂ) + t * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    norm_num at hre
  have hA := pcst_analyticAt_LFunction χ hne1
  have hne : DirichletCharacter.LFunction χ ((-1 / 2 : ℂ) + t * Complex.I) ≠ 0 := by
    rw [pcst_LFunction_factorization (s := (-1 / 2 : ℂ) + t * Complex.I) χ hne1]
    refine mul_ne_zero
      (LeanLab.Linnik.ExplicitFormula.no_zero_left_line χ.primitiveCharacter_isPrimitive t) ?_
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pcst_prime_factor_ne_zero χ p hp (by simp)
  have hc : ContinuousAt (logDeriv (DirichletCharacter.LFunction χ))
      ((-1 / 2 : ℂ) + t * Complex.I) :=
    hA.deriv.continuousAt.div hA.continuousAt hne
  exact ContinuousAt.comp (f := fun t : ℝ => (-1 / 2 : ℂ) + t * Complex.I) hc (by fun_prop)

/-- Continuity of the continued Gaussian transform on the line of real part minus one half. -/
private theorem pcst_continuedGaussian_line_continuous (δ : ℝ) :
    Continuous (fun t : ℝ => continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)) := by
  have h1 : Continuous (fun t : ℝ =>
      gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 1)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : 0 < ((((-1 / 2 : ℂ) + t * Complex.I) + 1)).re := by simp; norm_num
    exact ContinuousAt.comp (f := fun t : ℝ => ((-1 / 2 : ℂ) + t * Complex.I) + 1)
      (Continuation457.gaussian_mellin_differentiable δ _ hre).continuousAt (by fun_prop)
  have h2 : Continuous (fun t : ℝ =>
      gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : 0 < ((((-1 / 2 : ℂ) + t * Complex.I) + 2)).re := by simp; norm_num
    exact ContinuousAt.comp (f := fun t : ℝ => ((-1 / 2 : ℂ) + t * Complex.I) + 2)
      (Continuation457.gaussian_mellin_differentiable δ _ hre).continuousAt (by fun_prop)
  have hnum : Continuous (fun t : ℝ =>
      gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (((-1 / 2 : ℂ) + t * Complex.I) + 1)) :=
    h2.sub (h1.const_mul _)
  have hden : Continuous (fun t : ℝ => (-1 / 2 : ℂ) + t * Complex.I) := by fun_prop
  have hdenne : ∀ t : ℝ, (-1 / 2 : ℂ) + t * Complex.I ≠ 0 := by
    intro t h
    have hre : (-1 / 2 : ℝ) = 0 := by simpa using congrArg Complex.re h
    norm_num at hre
  exact (hnum.div hden hdenne).congr fun t => rfl

/-- `log (|t| + 3)` is dominated by a quarter power of `1 + |t|`. -/
private theorem pcst_log_shape (t : ℝ) :
    Real.log (|t| + 3) ≤ 12 * (1 + |t|) ^ (1 / 4 : ℝ) := by
  set a := |t| with ha
  have ha0 : 0 ≤ a := abs_nonneg t
  have hpos : 0 < 1 + a := by positivity
  have hlog := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ a + 3)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hr : (a + 3) ^ (1 / 4 : ℝ) ≤ ((1 + a) * 3) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by norm_num : (1 / 4 : ℝ) ≤ 1)
    simpa using h
  have hfin : (a + 3) ^ (1 / 4 : ℝ) ≤ 3 * (1 + a) ^ (1 / 4 : ℝ) := by
    calc (a + 3) ^ (1 / 4 : ℝ) ≤ ((1 + a) * 3) ^ (1 / 4 : ℝ) := hr
      _ = (1 + a) ^ (1 / 4 : ℝ) * 3 ^ (1 / 4 : ℝ) := Real.mul_rpow hpos.le (by norm_num)
      _ ≤ (1 + a) ^ (1 / 4 : ℝ) * 3 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hpos.le _)
      _ = 3 * (1 + a) ^ (1 / 4 : ℝ) := by ring
  calc Real.log (a + 3) ≤ (a + 3) ^ (1 / 4 : ℝ) / (1 / 4) := hlog
    _ = 4 * (a + 3) ^ (1 / 4 : ℝ) := by ring
    _ ≤ 4 * (3 * (1 + a) ^ (1 / 4 : ℝ)) := by linarith
    _ = 12 * (1 + a) ^ (1 / 4 : ℝ) := by ring

/-! ### D. The line of real part minus one half is an admissible contour -/

/-- LEAF. The integrand of step three is integrable on the line of real part minus one
half: the continued Gaussian transform decays faster than any power in the height, the
logarithmic derivative grows only like the logarithm of the height, and the scale factor
has the constant modulus `x ^ (-1 / 2)`.  This is one integrability statement and nothing
else; it fixes no value of the integral, no residue and no zero sum, and it needs no
hypothesis on the zeros. -/
theorem principal_half_line_integrable (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  haveI : NeZero (DirichletCharacter.conductor χ) :=
    ⟨DirichletCharacter.conductor_ne_zero (χ := χ)⟩
  obtain ⟨Cg, hCg, hGdec⟩ := pcst_continuedGaussian_decay δ
  obtain ⟨CL, hCL, hLb⟩ := pcst_logDeriv_LFunction_bound q χ
  have hcont : Continuous (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
    have h3 : Continuous (fun t : ℝ => (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact ContinuousAt.comp (f := fun t : ℝ => ((-1 / 2 : ℂ) + t * Complex.I))
        (continuousAt_const_cpow (by exact_mod_cast hx0.ne')) (by fun_prop)
    exact ((pcst_logDeriv_LFunction_continuous q χ).mul
      (pcst_continuedGaussian_line_continuous δ)).mul h3
  set M : ℝ := max 1 (Real.log q) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  have hlogqM : Real.log q ≤ M := le_max_right _ _
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-(7 / 4 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (7 / 4 : ℝ)) (by norm_num))
  refine (hbase.const_mul (Cg * CL * (26 * M))).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hu1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hu0 : (0 : ℝ) < 1 + |t| := by linarith
  have hA1 : (1 : ℝ) ≤ (1 + |t|) ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hu1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa using h
  have hA4 : (1 + |t|) ^ (1 / 4 : ℝ) * (1 + |t|) ^ (-(2 : ℝ)) = (1 + |t|) ^ (-(7 / 4 : ℝ)) := by
    rw [show (-(7 / 4) : ℝ) = 1 / 4 + (-(2 : ℝ)) by norm_num, Real.rpow_add hu0]
  -- the logarithmic factor
  have hLt : Real.log (q * (|t| + 2)) ≤ 13 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hlogsplit : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
      Real.log_mul (by linarith) (by positivity)
    have hmono : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hrpow : Real.log (|t| + 3) ≤ 12 * (1 + |t|) ^ (1 / 4 : ℝ) := pcst_log_shape t
    rw [hlogsplit]
    have hqa : Real.log q ≤ M * (1 + |t|) ^ (1 / 4 : ℝ) :=
      le_trans hlogqM (le_mul_of_one_le_right hM0 hA1)
    have hmulA : (1 : ℝ) * (1 + |t|) ^ (1 / 4 : ℝ) ≤ M * (1 + |t|) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hM1 (Real.rpow_nonneg hu0.le _)
    have h2a : Real.log (|t| + 2) ≤ 12 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by
      have h12 : 12 * (1 + |t|) ^ (1 / 4 : ℝ) ≤ 12 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by
        nlinarith [hmulA]
      linarith
    have hsum : M * (1 + |t|) ^ (1 / 4 : ℝ) + 12 * M * (1 + |t|) ^ (1 / 4 : ℝ)
        = 13 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by ring
    linarith [hqa, h2a, hsum]
  have hL1 : ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ)) := by
    have h := hLb t
    have hCL0 : 0 ≤ CL := hCL
    calc ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖
        ≤ CL * Real.log (q * (|t| + 2)) := h
      _ ≤ CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hLt hCL0
  have hG1 : ‖continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      Cg * (2 * (1 + |t|) ^ (-(2 : ℝ))) := by
    have h := hGdec t
    have h1 : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
      have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
      nlinarith [sq_nonneg (|t| - 1)]
    have hdec : 1 / (1 + t ^ 2) ≤ 2 * (1 + |t|) ^ (-(2 : ℝ)) := by
      have h2 : (1 + |t|) ^ (-(2 : ℝ)) = 1 / (1 + |t|) ^ 2 := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
      rw [h2, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h1]
    calc ‖continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Cg / (1 + t ^ 2) := h
      _ = Cg * (1 / (1 + t ^ 2)) := by ring
      _ ≤ Cg * (2 * (1 + |t|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hdec hCg.le
  have hP1 : ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, zero_mul, sub_zero, add_zero]
    calc x ^ (-1 / 2 : ℝ) ≤ x ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = 1 := Real.rpow_zero x
  rw [norm_mul, norm_mul]
  have hstep : ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I)‖ *
      ‖continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I)‖ *
        ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      (CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ))) *
        (Cg * (2 * (1 + |t|) ^ (-(2 : ℝ)))) * 1 := by
    have hMA : 0 ≤ 13 * M * (1 + |t|) ^ (1 / 4 : ℝ) := by
      have h1 : 0 ≤ 13 * M := by linarith
      exact mul_nonneg h1 (Real.rpow_nonneg (by linarith [abs_nonneg t]) _)
    have hb_nonneg : 0 ≤ CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ)) := mul_nonneg hCL hMA
    have hd_nonneg : 0 ≤ Cg * (2 * (1 + |t|) ^ (-(2 : ℝ))) :=
      mul_nonneg hCg.le (by positivity)
    exact mul_le_mul (mul_le_mul hL1 hG1 (norm_nonneg _) hb_nonneg) hP1 (norm_nonneg _)
      (mul_nonneg hb_nonneg hd_nonneg)
  have heq : (CL * (13 * M * (1 + |t|) ^ (1 / 4 : ℝ))) *
      (Cg * (2 * (1 + |t|) ^ (-(2 : ℝ)))) * 1 = (Cg * CL * (26 * M)) * (1 + |t|) ^ (-(7 / 4 : ℝ)) := by
    rw [← hA4]
    ring
  linarith [hstep, heq]

/-! ### E. The assembly -/

/-- The contour shift identity of the target, assembled from the three identities above by
rewriting and `ring` only.  The statement is the target's, unchanged; the assembly has no
sorry of its own and does not use the target theorem. -/
theorem principal_contour_shift_two_to_minus_half_split (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hq : q = 1) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) =
      ((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) +
        (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T -
        (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
  have h1 := principal_two_line_prime_sum x hx q χ δ
  have h2 := principal_half_line_conductor_one x hx q χ δ hq
  have h3 := principal_explicit_formula_shift x hx q χ δ T hq
  rw [h1, h3, h2]
  ring

end LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_two_line_prime_sum
#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_explicit_formula_shift
#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_half_line_conductor_one
#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_half_line_integrable
#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_contour_shift_two_to_minus_half_split
