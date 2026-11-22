import Mathlib

/-!
PREP 2026-11-22, burst-20261122 unit P1122-0077: split of the cited leaf
`Prep1121VIPointwiseA.binet_formula`, Binet's second formula for the digamma function,
OLBC10 DLMF 5.9.15, quoted by P0014 Helfgott, Major arcs for Goldbach's problem,
arXiv 1305.2897v4, page 34, display 4.10, first line.

Route: DLMF 5.9.13 writes ψ(z) - ln z as a Laplace transform of 1/t - 1/(1 - e^{-t}).
That kernel equals -1/2 - 2 ∫_0^∞ sin(tτ)/(e^{2πτ} - 1) dτ by GR00 3.911.2 at β = 2π,
and the Laplace transform of sin(tτ) in t is τ/(τ² + z²). Fubini then gives DLMF 5.9.15.
Leaves carry the doc tag LEAF; `binet_formula` is assembled here with no sorry of its own,
with the exact statement of the parent leaf. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1122BinetSplit
open Complex MeasureTheory Set

/-- LEAF: OLBC10 DLMF 5.9.13, the Laplace form of the digamma function from which Binet's
second formula DLMF 5.9.15, quoted at P0014 page 34 display 4.10 first line, is derived:
for re z above 0, ψ(z) = ln z + ∫_0^∞ (1/t - 1/(1 - e^{-t})) e^{-tz} dt.
It follows from Gauss's integral DLMF 5.9.12 and Frullani's integral for ln z.
Class HARD: the digamma series, a complex Frullani integral and dominated convergence. -/
theorem digamma_log_laplace (z : ℂ) (hz : 0 < z.re) :
    digamma z = Complex.log z +
      ∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z) := by
  sorry

/-- LEAF: GR00 3.911.2, the sine integral against the Planck weight, the step from DLMF
5.9.13 to DLMF 5.9.15 quoted at P0014 page 34 display 4.10 first line: for a and β
positive, ∫_0^∞ sin(at)/(e^{βt} - 1) dt = (π/(2β)) coth(aπ/β) - 1/(2a).
Class MEDIUM: expand 1/(e^{βt} - 1) as the sum of e^{-nβt} over n ≥ 1, integrate termwise
under |sin(at)| ≤ at, ∫_0^∞ sin(at) e^{-nβt} dt = a/(a² + n²β²), and sum with the
partial fractions of the cotangent, Mathlib's `cot_series_rep`. -/
theorem sine_planck (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ∫ t in Ioi (0 : ℝ), Real.sin (a * t) / (Real.exp (β * t) - 1) =
      Real.pi / (2 * β) * (Real.cosh (a * Real.pi / β) / Real.sinh (a * Real.pi / β)) -
        1 / (2 * a) := by
  sorry

/-- LEAF: the Laplace transform of the sine, ∫_0^∞ e^{-uz} sin(ut) du = t/(t² + z²) for
real t and re z above 0, the inner integral of the interchange step from DLMF 5.9.13 to
DLMF 5.9.15, P0014 page 34 display 4.10 first line. Class EASY. PROVED here. -/
theorem laplace_sin (t : ℝ) (z : ℂ) (hz : 0 < z.re) :
    ∫ u in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * z) * (Real.sin (u * t) : ℂ) =
      (t : ℂ) / ((t : ℂ) ^ 2 + z ^ 2) := by
  have hA : (-z + t * I).re < 0 := by simp; linarith
  have hB : (-z - t * I).re < 0 := by simp; linarith
  have hpt : ∀ u : ℝ, Complex.exp (-(u : ℂ) * z) * (Real.sin (u * t) : ℂ) =
      (I / 2) * (Complex.exp ((-z - t * I) * u) - Complex.exp ((-z + t * I) * u)) := by
    intro u
    have e1 : Complex.exp ((-z - t * I) * u) =
        Complex.exp (-(u : ℂ) * z) * Complex.exp (-(((u * t : ℝ) : ℂ)) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp ((-z + t * I) * u) =
        Complex.exp (-(u : ℂ) * z) * Complex.exp (((u * t : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1, e2, Complex.ofReal_sin, Complex.sin]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub (integrableOn_exp_mul_complex_Ioi hB 0)
    (integrableOn_exp_mul_complex_Ioi hA 0), integral_exp_mul_complex_Ioi hB,
    integral_exp_mul_complex_Ioi hA]
  have h1 : z + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : z - t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (t : ℂ) ^ 2 + z ^ 2 = (z + t * I) * (z - t * I) := by
    ring_nf; rw [I_sq]; ring
  have hB' : -z - t * I = -(z + t * I) := by ring
  have hA' : -z + t * I = -(z - t * I) := by ring
  rw [h3, hB', hA']
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [div_neg, div_neg, neg_div, neg_div, neg_neg, neg_neg, div_sub_div _ _ h1 h2,
    eq_div_iff (mul_ne_zero h1 h2), mul_assoc, div_mul_cancel₀ _ (mul_ne_zero h1 h2)]
  ring_nf
  rw [I_sq]
  ring

/-- The kernel identity behind DLMF 5.9.13 to 5.9.15: for t positive,
1/t - 1/(1 - e^{-t}) = -1/2 - 2((π/(4π)) coth(tπ/(2π)) - 1/(2t)),
the right side being -1/2 - 2 ∫_0^∞ sin(tτ)/(e^{2πτ} - 1) dτ by `sine_planck`. -/
private lemma kernel_eq (t : ℝ) (ht : 0 < t) :
    1 / t - 1 / (1 - Real.exp (-t)) =
      -1 / 2 - 2 * (Real.pi / (2 * (2 * Real.pi)) *
        (Real.cosh (t * Real.pi / (2 * Real.pi)) / Real.sinh (t * Real.pi / (2 * Real.pi))) -
          1 / (2 * t)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hq : Real.pi / (2 * (2 * Real.pi)) = 1 / 4 := by field_simp; ring
  have hh : t * Real.pi / (2 * Real.pi) = t / 2 := by field_simp
  rw [hq, hh, Real.cosh_eq, Real.sinh_eq]
  set w := Real.exp (t / 2) with hw
  have hw1 : 1 < w := Real.one_lt_exp_iff.mpr (by linarith)
  have hw0 : 0 < w := by linarith
  have hneg : Real.exp (-(t / 2)) = w⁻¹ := by rw [Real.exp_neg]
  have hnegt : Real.exp (-t) = (w ^ 2)⁻¹ := by
    rw [hw, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  rw [hneg, hnegt]
  have hwne : w ≠ 0 := hw0.ne'
  have hw2 : w ^ 2 - 1 ≠ 0 := by nlinarith
  have hwd : w - w⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : w * w = 1 := by
      have h0 := mul_inv_cancel₀ hwne
      rw [← h] at h0; exact h0
    nlinarith
  have hwd' : 1 - (w ^ 2)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : w ^ 2 = 1 := by rw [eq_comm, inv_eq_one] at h; exact h
    nlinarith
  have htne : t ≠ 0 := ht.ne'
  field_simp
  ring

/-- The bound τ/(e^{2πτ} - 1) ≤ e^{-πτ}/(2π) for τ positive, from sinh y ≥ y. -/
private lemma planck_le (τ : ℝ) (hτ : 0 < τ) :
    τ / (Real.exp (2 * Real.pi * τ) - 1) ≤ Real.exp (-(Real.pi * τ)) / (2 * Real.pi) := by
  have hy : 0 ≤ Real.pi * τ := by positivity
  have hs := (Real.self_le_sinh_iff (x := Real.pi * τ)).mpr hy
  rw [Real.sinh_eq] at hs
  have hE : 0 < Real.exp (2 * Real.pi * τ) - 1 := by
    have : 1 < Real.exp (2 * Real.pi * τ) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hsplit : Real.exp (2 * Real.pi * τ) = Real.exp (Real.pi * τ) * Real.exp (Real.pi * τ) := by
    rw [← Real.exp_add]; ring_nf
  have hprod : Real.exp (Real.pi * τ) * Real.exp (-(Real.pi * τ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.pi_pos
  have hepos := Real.exp_pos (Real.pi * τ)
  have hnpos := Real.exp_pos (-(Real.pi * τ))
  rw [div_le_div_iff₀ hE (by positivity)]
  -- τ · 2π ≤ e^{-y}(e^{2y} - 1) = e^{y} - e^{-y}
  have key : Real.exp (-(Real.pi * τ)) * (Real.exp (2 * Real.pi * τ) - 1) =
      Real.exp (Real.pi * τ) - Real.exp (-(Real.pi * τ)) := by
    rw [hsplit]
    have : Real.exp (-(Real.pi * τ)) * (Real.exp (Real.pi * τ) * Real.exp (Real.pi * τ)) =
        Real.exp (Real.pi * τ) := by
      rw [← mul_assoc, mul_comm (Real.exp (-(Real.pi * τ))), hprod, one_mul]
    linarith [this]
  rw [key]
  nlinarith

/-- P0014 page 34, display 4.10, first line, OLBC10 DLMF 5.9.15: Binet's second formula,
with the exact statement of the parent leaf `Prep1121VIPointwiseA.binet_formula`.
Assembled from the leaves `digamma_log_laplace`, `sine_planck` and `laplace_sin` by
Fubini on the product of two half lines. -/
theorem binet_formula (z : ℂ) (hz : 0 < z.re) :
    digamma z = Complex.log z - 1 / (2 * z) -
      2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * t) : ℂ) - 1)) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set F : ℝ → ℝ → ℂ := fun t τ => Complex.exp (-(t : ℂ) * z) *
    ((Real.sin (t * τ) / (Real.exp (2 * Real.pi * τ) - 1) : ℝ) : ℂ) with hF
  -- integrability of e^{-tz} on the half line, and its integral 1/z
  have hz' : (-z).re < 0 := by simp; linarith
  have hexp_eq : (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) =
      fun t : ℝ => Complex.exp (-z * t) := by funext t; ring_nf
  have hexpI : Integrable (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) μ := by
    rw [hexp_eq]; exact integrableOn_exp_mul_complex_Ioi hz' 0
  have hexpV : ∫ t, Complex.exp (-(t : ℂ) * z) ∂μ = 1 / z := by
    rw [hexp_eq, hμ, integral_exp_mul_complex_Ioi hz' 0]
    simp
  -- integrability of F on the product of half lines
  have hg1 : Integrable (fun t : ℝ => t * Real.exp (-(z.re * t))) μ := by
    refine Integrable.of_integral_ne_zero ?_
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := z.re) (by norm_num) hz
    have hc : ∫ t, t * Real.exp (-(z.re * t)) ∂μ =
        ∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(z.re * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [hc, h, Real.Gamma_two]
    positivity
  have hg2 : Integrable (fun τ : ℝ => Real.exp (-(Real.pi * τ)) / (2 * Real.pi)) μ := by
    refine Integrable.div_const ?_ _
    have := integrableOn_exp_mul_Ioi (a := -Real.pi) (by linarith [Real.pi_pos]) 0
    refine this.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have hG := hg1.mul_prod hg2
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    fun_prop
  have hFI : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine hG.mono' hFm.aestronglyMeasurable ?_
    rw [hμ, Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    obtain ⟨ht, hτ⟩ := hp
    have ht0 : (0 : ℝ) < p.1 := ht
    have hτ0 : (0 : ℝ) < p.2 := hτ
    have hE : 0 < Real.exp (2 * Real.pi * p.2) - 1 := by
      have : 1 < Real.exp (2 * Real.pi * p.2) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_of_pos hE]
    have hre : (-(p.1 : ℂ) * z).re = -(z.re * p.1) := by simp; ring
    rw [hre]
    have hsin : |Real.sin (p.1 * p.2)| ≤ p.1 * p.2 := by
      have := Real.abs_sin_le_abs (x := p.1 * p.2)
      rwa [abs_of_pos (mul_pos ht0 hτ0)] at this
    have hpl := planck_le p.2 hτ0
    have hq : |Real.sin (p.1 * p.2)| / (Real.exp (2 * Real.pi * p.2) - 1) ≤
        p.1 * (Real.exp (-(Real.pi * p.2)) / (2 * Real.pi)) := by
      calc |Real.sin (p.1 * p.2)| / (Real.exp (2 * Real.pi * p.2) - 1)
          ≤ p.1 * p.2 / (Real.exp (2 * Real.pi * p.2) - 1) :=
            div_le_div_of_nonneg_right hsin hE.le
        _ = p.1 * (p.2 / (Real.exp (2 * Real.pi * p.2) - 1)) := by ring
        _ ≤ p.1 * (Real.exp (-(Real.pi * p.2)) / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hpl ht0.le
    calc Real.exp (-(z.re * p.1)) * (|Real.sin (p.1 * p.2)| / (Real.exp (2 * Real.pi * p.2) - 1))
        ≤ Real.exp (-(z.re * p.1)) * (p.1 * (Real.exp (-(Real.pi * p.2)) / (2 * Real.pi))) :=
          mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
      _ = p.1 * Real.exp (-(z.re * p.1)) * (Real.exp (-(Real.pi * p.2)) / (2 * Real.pi)) := by
          ring
  -- the inner integral in τ, through GR00 3.911.2
  have hinner : ∀ t : ℝ, 0 < t →
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z) =
        -(1 / 2) * Complex.exp (-(t : ℂ) * z) - 2 * ∫ τ, F t τ ∂μ := by
    intro t ht
    have hI : ∫ τ, F t τ ∂μ = Complex.exp (-(t : ℂ) * z) *
        ((∫ τ in Ioi (0 : ℝ), Real.sin (t * τ) / (Real.exp (2 * Real.pi * τ) - 1) : ℝ) : ℂ) := by
      simp only [hF]
      rw [integral_const_mul, hμ, integral_complex_ofReal]
    rw [hI, sine_planck t (2 * Real.pi) ht (by positivity)]
    have hk := kernel_eq t ht
    have hc : (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) =
        ((1 / t - 1 / (1 - Real.exp (-t)) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, hk]
    push_cast
    ring
  -- the outer integral in t, through the Laplace transform of the sine
  have houter : ∀ τ : ℝ, 0 < τ →
      ∫ t, F t τ ∂μ =
        (τ : ℂ) / (((τ : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * τ) : ℂ) - 1)) := by
    intro τ hτ
    have hE : (Real.exp (2 * Real.pi * τ) : ℂ) - 1 ≠ 0 := by
      have : 1 < Real.exp (2 * Real.pi * τ) := Real.one_lt_exp_iff.mpr (by positivity)
      intro h
      have h' : ((Real.exp (2 * Real.pi * τ) - 1 : ℝ) : ℂ) = 0 := by
        rw [Complex.ofReal_sub, Complex.ofReal_one]; exact h
      rw [Complex.ofReal_eq_zero] at h'
      linarith
    have hpt : ∀ t : ℝ, F t τ = (1 / ((Real.exp (2 * Real.pi * τ) : ℂ) - 1)) *
        (Complex.exp (-(t : ℂ) * z) * (Real.sin (t * τ) : ℂ)) := by
      intro t
      simp only [hF]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_const_mul, hμ, laplace_sin τ z hz]
    field_simp
  -- assembly
  rw [digamma_log_laplace z hz]
  have hcongr : ∫ t in Ioi (0 : ℝ),
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z) =
      ∫ t, (-(1 / 2) * Complex.exp (-(t : ℂ) * z) - 2 * ∫ τ, F t τ ∂μ) ∂μ :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => hinner t ht)
  have hleft : Integrable (fun t => ∫ τ, F t τ ∂μ) μ := hFI.integral_prod_left
  rw [hcongr, integral_sub (hexpI.const_mul _) (hleft.const_mul _), integral_const_mul,
    integral_const_mul, hexpV, integral_integral_swap hFI]
  have hswap : ∫ τ, ∫ t, F t τ ∂μ ∂μ = ∫ τ in Ioi (0 : ℝ),
      (τ : ℂ) / (((τ : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * τ) : ℂ) - 1)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => houter τ hτ)
  rw [hswap]
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  field_simp
  ring

end LeanLab.HelfgottMajor.Prep1122BinetSplit
