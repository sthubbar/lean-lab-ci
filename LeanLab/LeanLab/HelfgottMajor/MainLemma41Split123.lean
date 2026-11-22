import LeanLab.HelfgottMajor.Prep1121ContourShift
import LeanLab.HelfgottMajor.CircleResidue669
import LeanLab.HelfgottMajor.Lemma41Kernel669
import LeanLab.HelfgottMajor.Lemma41Leaf123
import LeanLab.HelfgottMajor.Norm389

/-!
HELFGOTT MAIN THEOREM burst, session CLOUD-burst20261120c, unit lemma41, 2026-11-21.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Lemma 4.1, page 31,
displays 4.1 to 4.3, proved on pages 31 to 35, for the Gaussian weight η♥ of page 44, in the
lab's CORRECTED form `Lemma41Leaf123.lemma_4_1_gaussian_corrected`.

SPLIT of that sealed leaf along the proof of the paper into four LEAF steps:
1. `contour_shift`, pages 32 and 33, displays 4.4 and 4.7: Mellin inversion, the interchange
   of 4.4 and the shift of the line from re s = 3/2 to re s = -1/2, with the residue R at
   s = 0 written as a circle integral about 0.
2. `residue_at_zero`, page 33, displays 4.6, 4.8 and 4.9, with the lab's correction: the value
   of that residue, including the log x of the double pole for even χ and the conjugate.
3. `vertical_integral_bound`, pages 34 and 35, displays 4.10 to 4.15: the integral on
   re s = -1/2.
4. `laurent_c0_bound`, page 33, displays 4.5 and 4.6: the bound for the constant Laurent
   coefficient c0 of G_δ at 0. PROVED here from the moment bounds of Norm389.

The continuation of G_δ to re s = -1/2 is the one of page 32: s G_δ(s) is the Mellin transform
of -t f'(t), f(t) = η♥(t) e(δt), display 4.14; for re s above 0 it is gaussianMellin.
The assembly `lemma_4_1_gaussian_corrected_of_leaves` has the exact sealed statement.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainLemma41Split123
open Real MeasureTheory Set LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- LEAF: P0014 proof of Lemma 4.1, pages 32 and 33, displays 4.4 and 4.7. Mellin inversion,
as in IK04 4.106, the interchange of sum and integral of 4.4, and the shift of the line of
integration from re s = 3/2 to re s = -1/2, which crosses the pole of ζ at s = 1 for q = 1,
the non-trivial zeros ρ with their multiplicity, and s = 0, where the residue R of 4.7 is the
circle integral about 0 on a circle of radius r small enough that the integrand has no other
pole in the closed disc. With s = -1/2 + iτ the vertical integral (1/2πi) ∫ ds is
(1/2π) ∫ dτ. -/
theorem contour_shift (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0}) ∧
      Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T + highZeros χ δ x T +
          (2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r =
        -((2 * π : ℂ)⁻¹ *
          ∫ τ : ℝ, contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)) := by
  exact Prep1121ContourShift.contour_shift_of_leaves x hx q χ hχ δ T

open Classical in
/-- LEAF: P0014 proof of Lemma 4.1, page 33, displays 4.6, 4.8 and 4.9, and the case analysis
at the top of page 34, in the lab's CORRECTED form. The residue at s = 0 of
L'/L(s, χ) G_δ(s) x^s, with η♥(0) = 1: log 2π for q = 1, from ζ'(0)/ζ(0) = log 2π, MV07
p. 331; for q above 1 the constant term log(2π/q) + γ - L'/L(1, χ bar) of L'/L at 0 from the
functional equation 4.8, IK04 Thm. 4.15, which relates L(s, χ) to L(1 - s, χ bar), so the
conjugate of L'(1, χ)/L(1, χ); and for even χ, where L'/L has a simple pole with residue 1, the
double pole adds the log x of x^s = 1 + s log x + ..., which display 4.7 loses, and the
Laurent constant c0 of 4.6. -/
theorem residue_at_zero (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ r : ℝ) (hr : 0 < r)
    (hF : DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0})) :
    (2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r =
      (if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
          ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
            (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
              DirichletCharacter.LFunction χ 1)) +
        (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) + laurentC0 δ else 0) := by
  exact CircleResidue669.residue_at_zero_general x hx q χ hχ δ r hr hF

/-- LEAF: P0014 proof of Lemma 4.1, pages 34 and 35, displays 4.10 to 4.15, for η♥. On
re s = -1/2 the functional equation 4.8 with 4.9, the digamma bound 4.10 from OLBC10 5.9.15
and GR00 3.411.1, and the Dirichlet series bound 4.11 give 4.12; Cauchy-Schwarz, the numerical
integral 226.844 and Plancherel 4.15 give (1/2π) ∫ |L'/L(s, χ) G_δ(s)| dτ at most
(log q + 6.01)(|η'|₂ + 2π|δ||η|₂), with |η♥'|₂ = (√π/4)^(1/2) and |η♥|₂ = (√π/2)^(1/2). -/
theorem vertical_integral_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ : ℝ) :
    (2 * π)⁻¹ * ∫ τ : ℝ,
        ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
            DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
          contMellin δ (-1 / 2 + τ * Complex.I)‖ ≤
      (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) := by
  sorry

/-- PROVED. P0014 display 4.5 on page 33: |log t| ≤ (2/3)(t^(-1/2) + t^(1/2)) for t > 0. -/
theorem abs_log_le (t : ℝ) (ht : 0 < t) :
    |log t| ≤ 2 / 3 * (t ^ ((1 / 2 : ℝ) - 1) + t ^ (1 / 2 : ℝ)) := by
  set u := log t / 2 with hu
  have h1 : t ^ (1 / 2 : ℝ) = exp u := by
    rw [rpow_def_of_pos ht, hu]; ring_nf
  have h2 : t ^ ((1 / 2 : ℝ) - 1) = exp (-u) := by
    rw [rpow_def_of_pos ht, hu]; ring_nf
  rw [h1, h2, show log t = 2 * u by rw [hu]; ring]
  have hc : exp (-u) + exp u = 2 * cosh u := by rw [cosh_eq]; ring
  rw [hc, abs_mul, abs_two]
  have hsum := (Real.hasSum_cosh u)
  have hp : ∑ n ∈ Finset.range 3, u ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ cosh u :=
    sum_le_hasSum (Finset.range 3)
      (fun n _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity)) hsum
  simp [Finset.sum_range_succ, Nat.factorial] at hp
  have hv : |u| ^ 2 = u ^ 2 := sq_abs u
  have hv4 : |u| ^ 4 = u ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hv, ← pow_mul]
  have ha := abs_nonneg u
  nlinarith [sq_nonneg (|u| ^ 2 - 3 / 2), sq_nonneg (|u| - 6 / 5)]

/-- PROVED. P0014 page 33, displays 4.5 and 4.6, and page 44: the constant Laurent coefficient
c0 = -∫ f'(t) log t dt of G_δ at 0 has norm at most |f'(t) log t|₁, which by 4.5 is at most
(2/3)(|η'/√t|₁ + |η'√t|₁ + 2π|δ|(|η/√t|₁ + |η√t|₁)), the c0 of display 4.3, at most
`Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ|` by the moments of Norm389. -/
theorem laurent_c0_bound (δ : ℝ) :
    ‖laurentC0 δ‖ ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| := by
  have hint : ∀ {a : ℝ}, -1 < a →
      IntegrableOn (fun t : ℝ => t ^ a * exp (-t ^ 2 / 2)) (Ioi 0) := by
    intro a ha
    have := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) ha
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; congr 2; ring
  have i1 := hint (a := 1 / 2) (by norm_num)
  have i2 := hint (a := 3 / 2) (by norm_num)
  have i3 := hint (a := (1 / 2) - 1) (by norm_num)
  set B : ℝ → ℝ := fun t => 2 / 3 *
    ((t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2) + t ^ (3 / 2 : ℝ) * exp (-t ^ 2 / 2)) +
      2 * π * |δ| * (t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2) +
        t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2))) with hB
  have iB : IntegrableOn B (Ioi 0) :=
    ((i1.add i2).add ((i3.add i1).const_mul (2 * π * |δ|))).const_mul (2 / 3)
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ‖((-(t : ℂ) + 2 * π * Complex.I * δ) * (exp (-t ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * t)) *
        (log t : ℂ)‖ ≤ B t := by
    intro t ht
    change 0 < t at ht
    have he : ‖LeanLab.HelfgottArcs.e (δ * t)‖ = 1 := by simp [LeanLab.HelfgottArcs.e, Complex.norm_exp]
    have hn : ‖-(t : ℂ) + 2 * π * Complex.I * δ‖ ≤ t + 2 * π * |δ| := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      simp [Complex.norm_real, abs_of_pos pi_pos]
    have hl := abs_log_le t ht
    have hE : 0 < exp (-t ^ 2 / 2) := exp_pos _
    rw [norm_mul, norm_mul, norm_mul, he, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hE]
    have hp1 : t * t ^ ((1 / 2 : ℝ) - 1) = t ^ (1 / 2 : ℝ) := by
      conv_lhs => lhs; rw [← rpow_one t]
      rw [← rpow_add ht]; norm_num
    have hp2 : t * t ^ (1 / 2 : ℝ) = t ^ (3 / 2 : ℝ) := by
      conv_lhs => lhs; rw [← rpow_one t]
      rw [← rpow_add ht]; norm_num
    have hpos1 : 0 ≤ t ^ ((1 / 2 : ℝ) - 1) := (rpow_pos_of_pos ht _).le
    have hpos2 : 0 ≤ t ^ (1 / 2 : ℝ) := (rpow_pos_of_pos ht _).le
    have hd : 0 ≤ 2 * π * |δ| := by positivity
    calc ‖-(t : ℂ) + 2 * π * Complex.I * δ‖ * exp (-t ^ 2 / 2) * |log t|
        ≤ (t + 2 * π * |δ|) * exp (-t ^ 2 / 2) *
            (2 / 3 * (t ^ ((1 / 2 : ℝ) - 1) + t ^ (1 / 2 : ℝ))) := by
          gcongr
      _ = B t := by
          rw [hB]; simp only
          rw [← hp2, ← hp1]; ring
  have hmain : ‖laurentC0 δ‖ ≤ ∫ t in Ioi (0 : ℝ), B t := by
    rw [laurentC0, norm_neg]
    exact norm_integral_le_of_norm_le iB
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt))
  have j12 : IntegrableOn (fun t : ℝ => t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2) +
      t ^ (3 / 2 : ℝ) * exp (-t ^ 2 / 2)) (Ioi 0) := i1.add i2
  have j31 : IntegrableOn (fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2) +
      t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2)) (Ioi 0) := i3.add i1
  have j31' : IntegrableOn (fun t : ℝ => 2 * π * |δ| *
      (t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2) + t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2)))
      (Ioi 0) := j31.const_mul _
  have hval : (∫ t in Ioi (0 : ℝ), B t) = 2 / 3 *
      (((∫ t in Ioi (0 : ℝ), t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2)) +
        ∫ t in Ioi (0 : ℝ), t ^ (3 / 2 : ℝ) * exp (-t ^ 2 / 2)) +
        2 * π * |δ| * ((∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2)) +
          ∫ t in Ioi (0 : ℝ), t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2))) := by
    rw [hB, integral_const_mul, integral_add j12 j31', integral_add i1 i2, integral_const_mul,
      integral_add i3 i1]
  have m1 := WeightedMoment389.gaussian_half_power_bound
  have m2 := Moment389.three_halves_moment_bound
  have m3 := HalfMoment389.gaussian_half_moment_bound
  have hd : 0 ≤ 2 * π * |δ| := by positivity
  refine hmain.trans (hval.le.trans ?_)
  unfold Lemma41Terms.c0
  have := mul_le_mul_of_nonneg_left (add_le_add m3 m1) hd
  nlinarith

open Classical in
/-- PROVED from the four LEAF steps above: the exact statement of the sealed
Lemma41Leaf123.lemma_4_1_gaussian_corrected, P0014 Lemma 4.1, page 31, displays 4.1 to 4.3,
for η♥ of page 44, in CORRECTED form. The error c is the Laurent constant c0 for even χ with
q above 1 and 0 otherwise. -/
theorem lemma_4_1_gaussian_corrected_of_leaves (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    ∃ c : ℂ, ‖c‖ ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T +
        ((if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
            ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
              (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
                DirichletCharacter.LFunction χ 1)) +
          (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0) + c)‖ ≤
        (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) / sqrt x := by
  classical
  have hx0 : 0 < x := by linarith
  obtain ⟨r, hr, hF, hshift⟩ := contour_shift x hx q χ hχ δ T
  have hres := residue_at_zero x hx q χ hχ δ r hr hF
  have hc0 : 0 ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| := by
    unfold Lemma41Terms.c0; have := pi_pos; positivity
  refine ⟨if q ≠ 1 ∧ χ.Even then laurentC0 δ else 0, ?_, ?_⟩
  · split_ifs
    · exact laurent_c0_bound δ
    · simpa using hc0
  · have hsplit : ((if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
            ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
              (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
                DirichletCharacter.LFunction χ 1)) +
          (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0) +
          (if q ≠ 1 ∧ χ.Even then laurentC0 δ else 0)) =
        (2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r := by
      rw [hres]; split_ifs <;> ring
    rw [hsplit, hshift, norm_neg, norm_mul]
    have hnorm : ∀ τ : ℝ, ‖contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)‖ =
        ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
            DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
          contMellin δ (-1 / 2 + τ * Complex.I)‖ * (sqrt x)⁻¹ := by
      intro τ
      rw [contourIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 1
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      rw [sqrt_eq_rpow, ← rpow_neg hx0.le]
      norm_num
    have hI := norm_integral_le_integral_norm (μ := volume)
      (fun τ : ℝ => contourIntegrand χ δ x (-1 / 2 + τ * Complex.I))
    simp_rw [hnorm] at hI
    rw [integral_mul_const] at hI
    have hV := vertical_integral_bound q χ hχ δ
    have hn2 : ‖((2 * π : ℂ))⁻¹‖ = (2 * π)⁻¹ := by
      rw [norm_inv]; congr 1
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hn2]
    have hs : 0 < (sqrt x)⁻¹ := inv_pos.mpr (sqrt_pos.mpr hx0)
    have hp : 0 < (2 * π)⁻¹ := by positivity
    calc (2 * π)⁻¹ * ‖∫ τ : ℝ, contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)‖
        ≤ (2 * π)⁻¹ * ((∫ τ : ℝ,
            ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
              DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
            contMellin δ (-1 / 2 + τ * Complex.I)‖) * (sqrt x)⁻¹) :=
          mul_le_mul_of_nonneg_left hI hp.le
      _ = ((2 * π)⁻¹ * ∫ τ : ℝ,
            ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
              DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
            contMellin δ (-1 / 2 + τ * Complex.I)‖) * (sqrt x)⁻¹ := by ring
      _ ≤ (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) *
            (sqrt x)⁻¹ := mul_le_mul_of_nonneg_right hV hs.le
      _ = _ := by ring

/-- PROVED, by rfl. Match check: the assembly has exactly the type of the sealed leaf
Lemma41Leaf123.lemma_4_1_gaussian_corrected. -/
theorem lemma_4_1_gaussian_corrected_of_leaves_type_match :
    type_of% @lemma_4_1_gaussian_corrected_of_leaves =
      type_of% @Lemma41Leaf123.lemma_4_1_gaussian_corrected := rfl

end LeanLab.HelfgottMajor.MainLemma41Split123

#print axioms LeanLab.HelfgottMajor.MainLemma41Split123.residue_at_zero
