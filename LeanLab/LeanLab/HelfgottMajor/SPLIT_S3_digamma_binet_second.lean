import Mathlib

/-!
Split of `BinetS3.digamma_binet_second` in
`LeanLab.HelfgottMajor.SPLIT_S3_digamma_binet_three_halves_le`, burst 20261127 S3, unit S3-08p2.

Binet's second formula, OLBC10 5.9.15: for `ℜ z > 0`,
`ψ(z) = log z - 1/(2z) - 2 ∫₀^∞ t dt / ((t² + z²)(e^{2πt} - 1))`.

Route, the classical uniqueness proof, compare Whittaker and Watson 12.32 and 12.33:
write `J(z)` for the integral and `f(z) = ψ(z) - (log z - 1/(2z) - 2 J(z))`.
* on the real half line `x > 0`, `f(x + 1) = f(x)`: from `ψ(x+1) = ψ(x) + 1/x`, PROVED in Mathlib
  as `Complex.digamma_apply_add_one`, and the difference equation of `J`, LEAF
  `binetJ_real_add_one`;
* `f(x + n) → 0` as `n → ∞`: from `J(x+n) → 0`, LEAF `binetJ_real_tendsto_zero`, and the real
  Stirling asymptotic `ψ(y) - log y + 1/(2y) → 0`, LEAF `digamma_real_stirling_tendsto`;
* so `f = 0` on `(0, ∞)`; `f` is holomorphic on `ℜ z > 0`, by `differentiableOn_digamma_re_pos`,
  PROVED, and LEAF `differentiableOn_binetJ`, and the identity principle
  `eq_zero_of_real_pos_eq_zero`, PROVED, extends `f = 0` to the half plane.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
namespace SqShortLeftLeaves
namespace BinetS3
namespace BinetSecondSplit
open Complex MeasureTheory Set Filter Topology
open scoped Real

/-- The Binet integral of OLBC10 5.9.15,
`J(z) = ∫₀^∞ t dt / ((t² + z²)(e^{2πt} - 1))`, the integral in display 4.10 of Helfgott
1305.2897 page 34. -/
noncomputable def binetJ (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) : ℂ) - 1))

/-- LEAF: the difference equation of the Binet integral on the real half line, the step of
Whittaker and Watson 12.32 that makes `log z - 1/(2z) - 2J(z)` satisfy the digamma recurrence:
for real `x > 0`,
`2 (J(x+1) - J(x)) = log(x+1) - log x - 1/(2(x+1)) - 1/(2x)`.
Class HARD: it follows from the Abel-Plana summation formula or from
`2t/(t²+x²) = 2 ∫₀^∞ e^{-xu} sin(tu) du` and `∫₀^∞ sin(tu)/(e^{2πt}-1) dt = (coth(u/2)/4 - 1/(2u))`,
OLBC10 5.9.13 to 5.9.15. -/
theorem binetJ_real_add_one (x : ℝ) (hx : 0 < x) :
    2 * (binetJ ((x : ℂ) + 1) - binetJ (x : ℂ)) =
      Complex.log ((x : ℂ) + 1) - Complex.log (x : ℂ) - 1 / (2 * ((x : ℂ) + 1)) -
        1 / (2 * (x : ℂ)) := by
  sorry

/-- LEAF: the Binet integral tends to zero along `x + n`, the step of Whittaker and Watson 12.32
used to fix the periodic difference: for real `x > 0`, `J(x + n) → 0` as `n → ∞`.
Class EASY: `|J(y)| ≤ y⁻² ∫₀^∞ t dt/(e^{2πt}-1) = 1/(24 y²)` for real `y > 0`. -/
theorem binetJ_real_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => binetJ ((x : ℂ) + n)) atTop (𝓝 0) := by
  sorry

/-- LEAF: the real Stirling asymptotic of the digamma function, OLBC10 5.11.2 to first order:
for real `x > 0`, `ψ(x + n) - log(x + n) + 1/(2(x + n)) → 0` as `n → ∞`.
Class MEDIUM: from `ψ(n+1) = H_n - γ`, Mathlib `Complex.digamma_nat_add_one`, the harmonic
asymptotic `H_n - log n → γ`, and the monotonicity of the real digamma function by
log convexity of `Γ`, Bohr and Mollerup. -/
theorem digamma_real_stirling_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => digamma ((x : ℂ) + n) - Complex.log ((x : ℂ) + n) +
      1 / (2 * ((x : ℂ) + n))) atTop (𝓝 0) := by
  sorry

/-- PROVED: the digamma function `Γ'/Γ` is holomorphic on the right half plane, where `Γ` is
holomorphic and zero free, from Mathlib `Complex.differentiableAt_Gamma` and
`Complex.Gamma_ne_zero`, with analyticity of `Γ` for its derivative. -/
theorem differentiableOn_digamma_re_pos :
    DifferentiableOn ℂ digamma {z : ℂ | 0 < z.re} := by
  intro z hz
  have hz' : 0 < z.re := hz
  have hpole : ∀ w : ℂ, 0 < w.re → ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro w hw m h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun w hw =>
    (differentiableAt_Gamma w (hpole w hw)).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ Gamma {z : ℂ | 0 < z.re} := hG.analyticOnNhd hopen
  have hdG : DifferentiableAt ℂ (deriv Gamma) z :=
    ((hGa z hz).deriv).differentiableAt
  have hne : Gamma z ≠ 0 := Gamma_ne_zero (hpole z hz)
  rw [digamma_def]
  have : logDeriv Gamma = fun w => deriv Gamma w / Gamma w := rfl
  rw [this]
  exact (hdG.div (differentiableAt_Gamma z (hpole z hz)) hne).differentiableWithinAt

/-- LEAF: the Binet integral `J` is holomorphic on the right half plane, the step of
Whittaker and Watson 12.32 that the integral defines an analytic function there.
Class MEDIUM: differentiation under the integral sign, the integrand being dominated near any
`z₀` with `ℜ z₀ > 0` by a multiple of `t/(e^{2πt}-1)` since `|t² + z²| ≥ (ℜ z)²`. -/
theorem differentiableOn_binetJ :
    DifferentiableOn ℂ binetJ {z : ℂ | 0 < z.re} := by
  sorry

/-- PROVED: the identity principle on the right half plane: a function holomorphic on `ℜ z > 0`
that vanishes on the positive real axis vanishes on the half plane, from Mathlib
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, the half plane being convex
and open and `1` an accumulation point of `(0, ∞)`. -/
theorem eq_zero_of_real_pos_eq_zero (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (h0 : ∀ x : ℝ, 0 < x → f (x : ℂ) = 0) (z : ℂ) (hz : 0 < z.re) : f z = 0 := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have han : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re} := hf.analyticOnNhd hopen
  have hconv : Convex ℝ {z : ℂ | 0 < z.re} := convex_halfSpace_re_gt 0
  have h1 : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  refine han.eqOn_zero_of_preconnected_of_frequently_eq_zero hconv.isPreconnected h1 ?_ hz
  have hreal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds |>.trans (by simp)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), f (x : ℂ) = 0 := by
    have hp : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), 0 < x := lt_mem_nhds one_pos
    exact (eventually_nhdsWithin_of_eventually_nhds hp).mono fun x hx => h0 x hx
  exact (hreal.frequently hev.frequently)

/-- PROVED from the leaves: Binet's second formula on the positive real axis. -/
theorem digamma_binet_second_real (x : ℝ) (hx : 0 < x) :
    digamma (x : ℂ) = Complex.log (x : ℂ) - 1 / (2 * (x : ℂ)) - 2 * binetJ (x : ℂ) := by
  set f : ℝ → ℂ := fun y => digamma (y : ℂ) -
    (Complex.log (y : ℂ) - 1 / (2 * (y : ℂ)) - 2 * binetJ (y : ℂ)) with hfdef
  have hstep : ∀ y : ℝ, 0 < y → f (y + 1) = f y := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hy1 : (y : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < y + 1 := by linarith
      exact_mod_cast this.ne'
    have hpole : ∀ m : ℕ, (y : ℂ) ≠ -(m : ℂ) := by
      intro m h
      have h' : y = -(m : ℝ) := by exact_mod_cast h
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hd := digamma_apply_add_one (y : ℂ) hpole
    have hJ := binetJ_real_add_one y hy
    simp only [hfdef]
    push_cast
    rw [hd]
    linear_combination hJ
  have hiter : ∀ n : ℕ, f (x + n) = f x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hxn : 0 < x + n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      rw [Nat.cast_succ, ← add_assoc, hstep _ hxn, ih]
  have hlim : Tendsto (fun n : ℕ => f (x + n)) atTop (𝓝 0) := by
    have h1 := digamma_real_stirling_tendsto x hx
    have h2 := (binetJ_real_tendsto_zero x hx).const_mul 2
    rw [mul_zero] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr (fun n => ?_)
    simp only [hfdef]
    push_cast
    ring
  have hconst : Tendsto (fun n : ℕ => f (x + n)) atTop (𝓝 (f x)) := by
    simp only [hiter]; exact tendsto_const_nhds
  have hfx : f x = 0 := tendsto_nhds_unique hconst hlim
  have := hfx
  simp only [hfdef] at this
  exact sub_eq_zero.mp this

/-- Assembly: Binet's second formula, OLBC10 5.9.15, with the exact statement of
`BinetS3.digamma_binet_second`. -/
theorem digamma_binet_second_split (z : ℂ) (hz : 0 < z.re) :
    digamma z = Complex.log z - 1 / (2 * z) -
      2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) : ℂ) - 1)) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  set F : ℂ → ℂ := fun w => digamma w - (Complex.log w - 1 / (2 * w) - 2 * binetJ w) with hF
  have hlog : DifferentiableOn ℂ Complex.log U := by
    intro w hw
    exact (Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hw))).differentiableWithinAt
  have hinv : DifferentiableOn ℂ (fun w : ℂ => 1 / (2 * w)) U := by
    intro w hw
    have hw0 : w ≠ 0 := by
      have hw' : 0 < w.re := hw
      intro h; rw [h] at hw'; simp at hw'
    refine (DifferentiableAt.div (differentiableAt_const _)
      ((differentiableAt_const _).mul differentiableAt_id) ?_).differentiableWithinAt
    simpa using hw0
  have hFd : DifferentiableOn ℂ F U :=
    differentiableOn_digamma_re_pos.sub
      ((hlog.sub hinv).sub (differentiableOn_binetJ.const_mul 2))
  have hF0 : ∀ x : ℝ, 0 < x → F (x : ℂ) = 0 := by
    intro x hx
    simp only [hF]
    rw [digamma_binet_second_real x hx]
    ring
  have h := eq_zero_of_real_pos_eq_zero F hFd hF0 z hz
  simp only [hF] at h
  exact sub_eq_zero.mp h

end BinetSecondSplit
end BinetS3
end SqShortLeftLeaves
end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.BinetS3.BinetSecondSplit.differentiableOn_digamma_re_pos
#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.BinetS3.BinetSecondSplit.eq_zero_of_real_pos_eq_zero
#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.BinetS3.BinetSecondSplit.digamma_binet_second_real
#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.BinetS3.BinetSecondSplit.digamma_binet_second_split
