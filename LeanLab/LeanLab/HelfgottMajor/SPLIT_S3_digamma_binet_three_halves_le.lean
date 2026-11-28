import Mathlib

/-!
Split of `SqShortLeftLeaves.digamma_binet_three_halves_le` in
`LeanLab.HelfgottMajor.SPLIT_logDeriv_zeta_left_short_le`, burst 20261127 S3, unit S3-08.

The target is display 4.10 of Helfgott, arXiv 1305.2897, page 34, in its intermediate form:
for `ℜ z = 3/2`, `‖ψ(z) - (log z - 1/(2z))‖ ≤ 1/27`. The paper's proof has three inputs:

* LEAF `digamma_binet_second` is Binet's second formula, OLBC10 5.9.15, as cited by the paper;
  Mathlib has `digamma` only as `logDeriv Gamma` with no integral representation;
* `integrableOn_t_div_exp_two_pi_sub_one` and `integral_t_div_exp_two_pi_sub_one`, PROVED here,
  are the convergence and the value `∫₀^∞ t dt / (e^{2πt} - 1) = Γ(2) ζ(2) / (2π)² = 1/24`;
* the lower bound `|t² + z²| ≥ 9/4` for real `t` and `ℜ z = 3/2` is PROVED below, from
  `t² + z² = (z + it)(z - it)` and `ℜ(z ± it) = 3/2`.

The assembly `digamma_binet_three_halves_le_split` has no sorry of its own; the only open
input is the Binet leaf.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
namespace SqShortLeftLeaves
namespace BinetS3
open Complex MeasureTheory Set
open scoped Real

/-- LEAF: Binet's second formula for the digamma function, OLBC10 5.9.15, the formula Helfgott
1305.2897 page 34 cites for display 4.10: for `ℜ z > 0`,
`ψ(z) = log z - 1/(2z) - 2 ∫₀^∞ t dt / ((t² + z²)(e^{2πt} - 1))`, principal logarithm.
Class HARD: CITED-LEFT, a classical theorem not in Mathlib, whose `digamma` has no integral
representation. -/
theorem digamma_binet_second (z : ℂ) (hz : 0 < z.re) :
    digamma z = Complex.log z - 1 / (2 * z) -
      2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) : ℂ) - 1)) := by
  sorry

/-- PROVED: convergence of the integral of display 4.10 of Helfgott 1305.2897 page 34: the
function `t / (e^{2πt} - 1)` is integrable on `(0, ∞)`. It is at most `e^{-πt}/(2π)` since
`e^x - 1 ≥ x e^{x/2}`, from `sinh x ≥ x`. -/
theorem integrableOn_t_div_exp_two_pi_sub_one :
    IntegrableOn (fun t : ℝ => t / (Real.exp (2 * π * t) - 1)) (Ioi 0) := by
  have hdom : IntegrableOn (fun t : ℝ => (1 / (2 * π)) * Real.exp (-π * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 Real.pi_pos).const_mul _
  refine hdom.mono' ?_ ?_
  · exact (measurable_id.div ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).measurable.sub_const 1)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    set x : ℝ := π * t with hx
    have hx0 : 0 < x := by positivity
    have hsinh : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0.le
    have hexp2 : Real.exp (2 * π * t) = Real.exp x * Real.exp x := by
      rw [← Real.exp_add]; congr 1; rw [hx]; ring
    have hinv : Real.exp (-π * t) * Real.exp x = 1 := by
      rw [← Real.exp_add, hx]; simp
    have hkey : 2 * x * Real.exp x ≤ Real.exp (2 * π * t) - 1 := by
      rw [hexp2]
      have hs : Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 := Real.sinh_eq x
      have h1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      have hp : 0 < Real.exp x := Real.exp_pos x
      nlinarith
    have he : 0 < Real.exp (2 * π * t) - 1 := by
      have : 0 < 2 * x * Real.exp x := by positivity
      linarith
    rw [Real.norm_eq_abs, abs_of_pos (div_pos ht0 he), div_le_iff₀ he]
    have hpe : 0 < Real.exp (-π * t) := Real.exp_pos _
    have hpi : 0 < π := Real.pi_pos
    have h2 : 1 / (2 * π) * Real.exp (-π * t) * (2 * x * Real.exp x) = t := by
      have e : 1 / (2 * π) * Real.exp (-π * t) * (2 * x * Real.exp x) =
          (Real.exp (-π * t) * Real.exp x) * (x / π) := by ring
      rw [e, hinv, one_mul, hx]
      field_simp
    have h3 : 1 / (2 * π) * Real.exp (-π * t) * (2 * x * Real.exp x) ≤
        1 / (2 * π) * Real.exp (-π * t) * (Real.exp (2 * π * t) - 1) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith

/-- PROVED: the value used in display 4.10 of Helfgott 1305.2897 page 34:
`∫₀^∞ t dt / (e^{2πt} - 1) = Γ(2) ζ(2) / (2π)² = 1/24`: expand
`1/(e^{2πt} - 1) = Σ_{k ≥ 1} e^{-2πkt}`, integrate termwise, and use `ζ(2) = π²/6`. -/
theorem integral_t_div_exp_two_pi_sub_one :
    ∫ t in Ioi (0 : ℝ), t / (Real.exp (2 * π * t) - 1) = 1 / 24 := by
  set c : ℝ := 2 * π with hc
  have hc0 : 0 < c := by positivity
  set F : ℕ → ℝ → ℝ := fun k t => t * Real.exp (-((c * ((k : ℝ) + 1)) * t)) with hF
  have hval : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), F k t = 1 / (c * ((k : ℝ) + 1)) ^ 2 := by
    intro k
    have hr : 0 < c * ((k : ℝ) + 1) := by positivity
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
    have e1 : ∀ t : ℝ, t ^ ((2 : ℝ) - 1) = t := fun t => by norm_num
    simp only [e1, Real.Gamma_two, mul_one] at h
    simp only [hF]
    rw [h, Real.rpow_two, div_pow, one_pow]
  have hint : ∀ k : ℕ, Integrable (F k) (volume.restrict (Ioi (0 : ℝ))) := by
    intro k
    refine Integrable.of_integral_ne_zero ?_
    rw [hval k]
    have : 0 < c * ((k : ℝ) + 1) := by positivity
    positivity
  have hnorm : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), ‖F k t‖ = 1 / (c * ((k : ℝ) + 1)) ^ 2 := by
    intro k
    rw [← hval k]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    simp only [hF]
    exact Real.norm_of_nonneg (by positivity)
  have hz : HasSum (fun k : ℕ => 1 / (((k : ℝ) + 1)) ^ 2) (π ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using h
  have hS : HasSum (fun k : ℕ => 1 / (c * ((k : ℝ) + 1)) ^ 2) (1 / c ^ 2 * (π ^ 2 / 6)) := by
    have := hz.mul_left (1 / c ^ 2)
    convert this using 1
    funext k
    rw [mul_pow]; field_simp
  have hsum : Summable fun k : ℕ => ∫ t in Ioi (0 : ℝ), ‖F k t‖ := by
    simp only [hnorm]; exact hS.summable
  have hmain := integral_tsum_of_summable_integral_norm hint hsum
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ∑' k : ℕ, F k t = t / (Real.exp (2 * π * t) - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    set r : ℝ := Real.exp (-(c * t)) with hrdef
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by
      rw [hrdef, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
    have hterm : ∀ k : ℕ, F k t = (t * r) * r ^ k := by
      intro k
      simp only [hF, hrdef]
      rw [← Real.exp_nat_mul, mul_assoc t, ← Real.exp_add]
      congr 2; ring
    have hrinv : r * Real.exp (c * t) = 1 := by
      rw [hrdef, ← Real.exp_add]; simp
    have hE : 0 < Real.exp (c * t) - 1 := by
      have : 1 < Real.exp (c * t) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    simp only [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, ← hc]
    have h1r : 0 < 1 - r := by linarith
    have h1e : (1 - r) * Real.exp (c * t) = Real.exp (c * t) - 1 := by
      linear_combination (-1 : ℝ) * hrinv
    rw [eq_div_iff hE.ne']
    calc t * r * (1 - r)⁻¹ * (Real.exp (c * t) - 1)
        = t * r * (1 - r)⁻¹ * ((1 - r) * Real.exp (c * t)) := by rw [h1e]
      _ = t * (r * Real.exp (c * t)) := by
        have := h1r.ne'
        field_simp
      _ = t := by rw [hrinv, mul_one]
  rw [← setIntegral_congr_fun measurableSet_Ioi hpt, ← hmain]
  simp only [hval]
  rw [hS.tsum_eq, hc]
  field_simp
  ring

/-- PROVED: the step `|t² + z²| ≥ 9/4` of display 4.10 of Helfgott 1305.2897 page 34, for real
`t` and `ℜ z = 3/2`. -/
theorem norm_sq_add_sq_ge (z : ℂ) (hz : z.re = 3 / 2) (t : ℝ) :
    9 / 4 ≤ ‖(t : ℂ) ^ 2 + z ^ 2‖ := by
  have hfac : (t : ℂ) ^ 2 + z ^ 2 = (z + t * I) * (z - t * I) := by
    ring_nf; rw [I_sq]; ring
  have h1 : 3 / 2 ≤ ‖z + t * I‖ := by
    have := Complex.abs_re_le_norm (z + t * I)
    simp [hz] at this
    rw [abs_of_pos (by norm_num : (0:ℝ) < 3 / 2)] at this
    exact this
  have h2 : 3 / 2 ≤ ‖z - t * I‖ := by
    have := Complex.abs_re_le_norm (z - t * I)
    simp [hz] at this
    rw [abs_of_pos (by norm_num : (0:ℝ) < 3 / 2)] at this
    exact this
  rw [hfac, norm_mul]
  nlinarith

/-- The target `digamma_binet_three_halves_le` from the three leaves and `norm_sq_add_sq_ge`. -/
theorem digamma_binet_three_halves_le_split (z : ℂ) (hz : z.re = 3 / 2) :
    ‖digamma z - (Complex.log z - 1 / (2 * z))‖ ≤ 1 / 27 := by
  have hpos : 0 < z.re := by rw [hz]; norm_num
  rw [digamma_binet_second z hpos]
  set F : ℝ → ℂ := fun t =>
    (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) : ℂ) - 1)) with hF
  set J : ℂ := ∫ t in Ioi (0 : ℝ), F t with hJ
  have hsimp : Complex.log z - 1 / (2 * z) - 2 * J
      - (Complex.log z - 1 / (2 * z)) = -(2 * J) := by ring
  rw [hsimp, norm_neg, norm_mul]
  have hbound : ∀ t ∈ Ioi (0 : ℝ),
      ‖F t‖ ≤ 4 / 9 * (t / (Real.exp (2 * π * t) - 1)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have he : 0 < Real.exp (2 * π * t) - 1 := by
      have : 1 < Real.exp (2 * π * t) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    have hn := norm_sq_add_sq_ge z hz t
    have hc : ((Real.exp (2 * π * t) : ℂ) - 1) = ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ) := by
      push_cast; ring
    simp only [hF]
    rw [hc, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos he]
    rw [div_le_iff₀ (by positivity)]
    have : t / (Real.exp (2 * π * t) - 1) * (Real.exp (2 * π * t) - 1) = t :=
      div_mul_cancel₀ t he.ne'
    nlinarith
  have hg : Integrable (fun t : ℝ => 4 / 9 * (t / (Real.exp (2 * π * t) - 1)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_t_div_exp_two_pi_sub_one.const_mul (4 / 9)
  have hI : ‖J‖ ≤
      ∫ t in Ioi (0 : ℝ), 4 / 9 * (t / (Real.exp (2 * π * t) - 1)) := by
    refine norm_integral_le_of_norm_le hg ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hbound)
  rw [integral_const_mul, integral_t_div_exp_two_pi_sub_one] at hI
  rw [Complex.norm_two]
  linarith

end BinetS3
end SqShortLeftLeaves
end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.BinetS3.integrableOn_t_div_exp_two_pi_sub_one
#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.BinetS3.integral_t_div_exp_two_pi_sub_one
#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.BinetS3.norm_sq_add_sq_ge
#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.BinetS3.digamma_binet_three_halves_le_split
