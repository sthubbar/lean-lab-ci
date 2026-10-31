/-
Unit U-1551, track T1, DECOMPOSE, run 20261026T1219Z-15327, 2026-10-26. PALOMAR line I5171.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Decomposition of the input `SmoothT2.HadamardK gZ` of
`LeanLab.Routes.U1508.goldbach_445_hsw_gZ` under RH:
`Σ_{j ∈ s} 4/(4 + (γ_i - γ_j)²) ≤ log |γ_i|` for every finite set `s` of zeros.

The textbook route, Davenport, Multiplicative Number Theory, chapter 12, equations (17) and (18):
the Hadamard product of `ξ(s) = s(s-1)/2 · π^{-s/2} Γ(s/2) ζ(s)` gives
`Re ζ'/ζ(s) = -Re 1/(s-1) + (1/2) log π - (1/2) Re ψ(s/2 + 1) + Σ_ρ Re 1/(s - ρ)`, with
multiplicity and absolutely convergent, LEAF `hadamard_re_sum_of` from the LEAVES `xi_growth`,
`xi_zero_iff`, `logDeriv_xi` and the cited Hadamard theorem `hadamard_logDeriv_order_one`;
`ξ(1-s) = ξ(s)` is PROVED here as `xi_one_sub`.
At `s = 5/2 + iγ` and under RH, `Re 1/(s - ρ_j) = 2/(4 + (γ - γ_j)²)`, the terms are positive,
so any finite partial sum of the kernel is at most twice the full sum. Then
`|ζ'/ζ(5/2 + it)| ≤ 3/10`, LEAF `logDeriv_bound_5half`, true value `0.28874` at `t = 0`;
`Re ψ(9/4 + iu) ≤ log|9/4 + iu| + 1/10`, LEAF `digamma_re_le`; and the real inequality LEAF
`final_numeric` for `|γ| ≥ 14`, which comes from `Ordinates14` under RH, the assembly
`Decomp1551c.ordinates14_gZ_of_RH`.

A float check: at `s = 5/2 + 20i` the identity of `hadamard_re_sum_of` reads `0.617322` against
`0.617312` from the first 150 zeros with an integral tail.

ASSEMBLY `hadamardK_gZ_of_RH`, CONDITIONAL ON the leaves here and in `Decomp1551c`.
-/
import Mathlib
import LeanLab.Routes.Decomp1551c

namespace LeanLab.Routes.Decomp1551b

open Complex Filter Topology
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx re_half_of_RH)
open LeanLab.ChirreHagen2025.SmoothKernel (K)

local notation "ζ" => riemannZeta

/-- Riemann's `ξ(s) = s(s-1)/2 · Λ(s)`, written with Mathlib's entire `completedRiemannZeta₀`:
`s(s-1)Λ(s) = s(s-1)Λ₀(s) + 1`, so `ξ(s) = (s(s-1)Λ₀(s) + 1)/2`. -/
noncomputable def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- `ξ(1-s) = ξ(s)`, from Mathlib's `completedRiemannZeta₀_one_sub`. Proved. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Cited, not proved in the lab: Hadamard's factorization theorem, Hadamard 1893, in the
logarithmic derivative form for an entire function of order at most one, Davenport,
Multiplicative Number Theory, chapter 11. If `f` is entire, `f 0 ≠ 0` and
`|f(s)| ≤ C exp(C |s| log(|s| + 2))`, then there is `B` with
`f'/f(s) = B + Σ_ρ (1/(s-ρ) + 1/ρ)` over the zeros with multiplicity, absolutely convergent,
wherever `f(s) ≠ 0`. Mathlib v4.35.0 has no Hadamard factorization. -/
theorem hadamard_logDeriv_order_one (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hg : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖f s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2))) :
    ∃ B : ℂ, ∀ s : ℂ, f s ≠ 0 →
      Summable (fun i : (Σ ρ : {ρ : ℂ // f ρ = 0}, Fin (analyticOrderNatAt f (ρ : ℂ))) =>
        1 / (s - (i.1 : ℂ)) + 1 / (i.1 : ℂ)) ∧
      logDeriv f s = B + ∑' i : (Σ ρ : {ρ : ℂ // f ρ = 0}, Fin (analyticOrderNatAt f (ρ : ℂ))),
        (1 / (s - (i.1 : ℂ)) + 1 / (i.1 : ℂ)) := by
  sorry

/-- LEAF. Unit U-1551. Davenport chapter 12, page 80, first displays: `ξ` has order one,
`|ξ(s)| ≤ C exp(C |s| log(|s| + 2))` for all `s`, from Stirling for `Γ(s/2)` and
`ζ(s) ≪ |s|` on `Re s ≥ 1/2`, with `ξ(1-s) = ξ(s)` for the other half plane. -/
theorem xi_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖xi s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  sorry

/-- LEAF. Unit U-1551. Davenport chapter 12, page 79: the zeros of `ξ` are exactly the zeros
of `ζ` in the critical strip, with the same multiplicity, since `s(s-1)/2 · π^{-s/2} Γ(s/2)`
is analytic and nonzero on `0 < Re s < 1`, and `ξ ≠ 0` off the strip. -/
theorem xi_zero_iff :
    (∀ ρ : ℂ, xi ρ = 0 ↔ (ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)) ∧
    (∀ ρ : ℂ, ζ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      analyticOrderNatAt xi ρ = analyticOrderNatAt ζ ρ) := by
  have heq : ∀ z : ℂ, 0 < z.re → z ≠ 1 → xi z =
      (z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) / 2) * riemannZeta z := by
    intro z hz hz1
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    have hG : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [riemannZeta_eq_completedRiemannZeta₀ hz0]
    unfold xi
    field_simp
    ring
  have hfac : ∀ z : ℂ, 0 < z.re → z ≠ 1 →
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) / 2 ≠ 0 := by
    intro z hz hz1
    apply div_ne_zero _ (by norm_num)
    apply mul_ne_zero _ (Gamma_ne_zero_of_re_pos (by simp; linarith))
    apply mul_ne_zero _ ((Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
    exact mul_ne_zero (by intro h; norm_num [h] at hz) (sub_ne_zero.mpr hz1)
  have hp : ∀ z : ℂ, 0 < z.re → z ≠ 1 → (xi z = 0 ↔ riemannZeta z = 0) := by
    intro z hz hz1
    rw [heq z hz hz1, mul_eq_zero, or_iff_right (hfac z hz hz1)]
  constructor
  · intro z
    constructor
    · intro hz
      have hz0 : z ≠ 0 := by intro h; subst z; norm_num [xi] at hz
      have hz1 : z ≠ 1 := by intro h; subst z; norm_num [xi] at hz
      have hre : 0 < z.re := by
        by_contra hn
        have hwr : 1 ≤ (1 - z).re := by simp; linarith
        have hw1 : 1 - z ≠ 1 := by intro h; apply hz0; linear_combination -h
        have hw0 := riemannZeta_ne_zero_of_one_le_re hwr
        have hsym : xi (1 - z) = xi z := by
          unfold xi
          rw [completedRiemannZeta₀_one_sub]
          ring
        exact hw0 ((hp (1 - z) (by linarith) hw1).mp (hsym.trans hz))
      have hzero := (hp z hre hz1).mp hz
      refine ⟨hzero, hre, ?_⟩
      by_contra hn
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hn) hzero
    · rintro ⟨hz, h0, h1⟩
      exact (hp z h0 (by intro h; norm_num [h] at h1)).mpr hz
  · intro z hz h0 h1
    let a : ℂ → ℂ := fun w => w * (w - 1) * (Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2) / 2
    have hza : z ≠ 1 := by intro h; norm_num [h] at h1
    have ha0 : a z ≠ 0 := hfac z h0 hza
    have ha : AnalyticAt ℂ a z := by
      apply DifferentiableOn.analyticAt _ ((isOpen_re_gt 0).mem_nhds h0)
      intro w hw
      change 0 < w.re at hw
      apply DifferentiableAt.differentiableWithinAt
      unfold a
      have hdG : DifferentiableAt ℂ (fun v : ℂ => Gamma (v / 2)) w :=
        (hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt.comp w (by fun_prop)
      have hdpi : DifferentiableAt ℂ (fun v : ℂ => (Real.pi : ℂ) ^ (-v / 2)) w :=
        (show DifferentiableAt ℂ (fun v : ℂ => -v / 2) w by fun_prop).const_cpow
          (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
      fun_prop
    have he : xi =ᶠ[𝓝 z] a * riemannZeta := by
      filter_upwards [(isOpen_re_gt 0).mem_nhds h0, isOpen_ne.mem_nhds hza] with w hw hw1
      exact heq w hw hw1
    have hζ : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hza
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr he, analyticOrderAt_mul ha hζ,
      analyticOrderAt_eq_zero.mpr (Or.inr ha0), zero_add]

/-- LEAF. Unit U-1551. Davenport chapter 12, logarithmic differentiation of
`ξ(s) = s(s-1)/2 · π^{-s/2} Γ(s/2) ζ(s)`: for `Re s > 1`,
`ξ'/ξ(s) = 1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2) + ζ'/ζ(s)`. -/
theorem logDeriv_xi (s : ℂ) (hs : 1 < s.re) :
    logDeriv xi s = 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2
      + logDeriv ζ s := by
  have heq : ∀ z : ℂ, 1 < z.re → xi z =
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) * riemannZeta z * (2 : ℂ)⁻¹ := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : 1 - z ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
    have hG : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hpi : (Real.pi : ℂ) ^ (-z / 2) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    rw [riemannZeta_eq_completedRiemannZeta₀ hz0]
    unfold xi
    field_simp
    ring
  have heq' : xi =ᶠ[𝓝 s] (fun z =>
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) * riemannZeta z * (2 : ℂ)⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact heq z hz
  rw [(logDeriv_congr_nhds heq').self_of_nhds, logDeriv_mul_const _ _ (by norm_num)]
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s - 1 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hG : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hdG : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s := by
    apply DifferentiableAt.comp s ((hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt)
    fun_prop
  have hdpi : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    exact (show DifferentiableAt ℂ (fun z : ℂ => -z / 2) s by fun_prop).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [logDeriv_fun_mul s (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1) hpi) hG)
    (riemannZeta_ne_zero_of_one_lt_re hs) (by fun_prop) (differentiableAt_riemannZeta (by intro h; norm_num [h] at hs))]
  rw [logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Gamma (z / 2)) s (mul_ne_zero (mul_ne_zero hs0 hs1) hpi) hG
    ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hdpi) hdG]
  rw [logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1))
    (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s (mul_ne_zero hs0 hs1) hpi (by fun_prop) hdpi]
  rw [logDeriv_fun_mul s hs0 hs1 (by fun_prop) (by fun_prop)]
  have hp : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_fun_comp (f := fun z : ℂ => (Real.pi : ℂ) ^ z)
      (g := fun z : ℂ => -z / 2) (by fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))) (by fun_prop)]
    simp only [Complex.logDeriv_const_cpow (ofReal_ne_zero.mpr Real.pi_ne_zero)]
    simp [← Complex.ofReal_log Real.pi_pos.le]
    ring
  have hgamma : logDeriv (fun z : ℂ => Gamma (z / 2)) s = digamma (s / 2) / 2 := by
    rw [logDeriv_fun_comp (f := Gamma) (g := fun z : ℂ => z / 2)
      (hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt (by fun_prop)]
    simp [← digamma_def, div_eq_mul_inv]
  rw [hp, hgamma]
  simp [logDeriv_apply]
  ring

/-- LEAF. Unit U-1551. Davenport chapter 12, equations (17) and (18), real part form: for
`Re s > 1`, `Σ_ρ Re 1/(s - ρ) = Re ζ'/ζ(s) + Re 1/(s-1) - (1/2) log π + (1/2) Re ψ(s/2 + 1)`,
the sum over the nontrivial zeros with multiplicity, as a `HasSum` over `ZIdx`. From
`hadamard_logDeriv_order_one` applied to `ξ`, `ξ(0) = 1/2`, the three hypotheses, `xi_one_sub`
for `Re B = -Σ_ρ Re 1/ρ`, and `ψ(s/2 + 1) = ψ(s/2) + 2/s`, Mathlib's `digamma_apply_add_one`.
The reindexing from the zeros of `ξ` to `ZIdx` uses the first two hypotheses. -/
theorem hadamard_re_sum_of
    (hg : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖xi s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)))
    (hz : (∀ ρ : ℂ, xi ρ = 0 ↔ (ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)) ∧
      (∀ ρ : ℂ, ζ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        analyticOrderNatAt xi ρ = analyticOrderNatAt ζ ρ))
    (hl : ∀ s : ℂ, 1 < s.re → logDeriv xi s = 1 / s + 1 / (s - 1)
      - (Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2 + logDeriv ζ s)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun i : ZIdx => (1 / (s - (i.1 : ℂ))).re)
      ((logDeriv ζ s).re + (1 / (s - 1)).re - Real.log Real.pi / 2
        + (digamma (s / 2 + 1)).re / 2) := by
  sorry

set_option maxHeartbeats 3200000
set_option maxRecDepth 2000

/-- LEAF. Unit U-1551. `|ζ'/ζ(5/2 + it)| ≤ Σ Λ(n) n^{-5/2} = -ζ'/ζ(5/2) = 0.28874 ≤ 3/10`,
from Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` and a finite sum with a tail
bound. -/
theorem logDeriv_bound_5half (t : ℝ) : ‖logDeriv ζ ((5 / 2 : ℂ) + t * I)‖ ≤ 3 / 10 := by
  -- Exact prime powers below 64, followed by a telescoped logarithmic tail.
  -- Rational logarithm bounds use twenty positive terms of the exponential series.
  let f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n)
  have hf0 : ∀ n, 0 ≤ f n := by intro n; exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hprefix : ∑ n ∈ Finset.range 64, f n ≤ (288/1000 : ℝ) := by
    change ∑ n ∈ Finset.range 64, ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ (288/1000 : ℝ)
    have l2 : Real.log 2 ≤ (6932/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 20, (6932/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l3 : Real.log 3 ≤ (10987/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (3 : ℝ) ≤ ∑ i ∈ Finset.range 20, (10987/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l5 : Real.log 5 ≤ (16095/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 20, (16095/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l7 : Real.log 7 ≤ (19460/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (7 : ℝ) ≤ ∑ i ∈ Finset.range 20, (19460/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l11 : Real.log 11 ≤ (23979/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (11 : ℝ) ≤ ∑ i ∈ Finset.range 20, (23979/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l13 : Real.log 13 ≤ (25650/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (13 : ℝ) ≤ ∑ i ∈ Finset.range 20, (25650/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l17 : Real.log 17 ≤ (28333/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (17 : ℝ) ≤ ∑ i ∈ Finset.range 20, (28333/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l19 : Real.log 19 ≤ (29445/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (19 : ℝ) ≤ ∑ i ∈ Finset.range 20, (29445/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l23 : Real.log 23 ≤ (31355/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (23 : ℝ) ≤ ∑ i ∈ Finset.range 20, (31355/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l29 : Real.log 29 ≤ (33673/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (29 : ℝ) ≤ ∑ i ∈ Finset.range 20, (33673/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l31 : Real.log 31 ≤ (34340/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (31 : ℝ) ≤ ∑ i ∈ Finset.range 20, (34340/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l37 : Real.log 37 ≤ (36110/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (37 : ℝ) ≤ ∑ i ∈ Finset.range 20, (36110/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l41 : Real.log 41 ≤ (37136/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (41 : ℝ) ≤ ∑ i ∈ Finset.range 20, (37136/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l43 : Real.log 43 ≤ (37613/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (43 : ℝ) ≤ ∑ i ∈ Finset.range 20, (37613/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l47 : Real.log 47 ≤ (38502/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (47 : ℝ) ≤ ∑ i ∈ Finset.range 20, (38502/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l53 : Real.log 53 ≤ (39703/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (53 : ℝ) ≤ ∑ i ∈ Finset.range 20, (39703/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l59 : Real.log 59 ≤ (40776/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (59 : ℝ) ≤ ∑ i ∈ Finset.range 20, (40776/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l61 : Real.log 61 ≤ (41109/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (61 : ℝ) ≤ ∑ i ∈ Finset.range 20, (41109/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    let b : ℕ → ℝ := fun n => ([(0/100000000 : ℝ),(0/100000000 : ℝ),(12254279/100000000 : ℝ),(7048371/100000000 : ℝ),(2166250/100000000 : ℝ),(2879249/100000000 : ℝ),(0/100000000 : ℝ),(1501089/100000000 : ℝ),(382947/100000000 : ℝ),(452140/100000000 : ℝ),(0/100000000 : ℝ),(597521/100000000 : ℝ),(0/100000000 : ℝ),(420955/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(67696/100000000 : ℝ),(237778/100000000 : ℝ),(0/100000000 : ℝ),(187128/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(123592/100000000 : ℝ),(0/100000000 : ℝ),(51504/100000000 : ℝ),(0/100000000 : ℝ),(29006/100000000 : ℝ),(0/100000000 : ℝ),(74352/100000000 : ℝ),(0/100000000 : ℝ),(64181/100000000 : ℝ),(11968/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(43364/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(34502/100000000 : ℝ),(0/100000000 : ℝ),(31022/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(25424/100000000 : ℝ),(0/100000000 : ℝ),(11579/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(19415/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(15251/100000000 : ℝ),(0/100000000 : ℝ),(14146/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ)].getD n 0)
    have hb : ∀ n ∈ Finset.range 64, ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ b n := by
      intro n hn
      have hn64 : n < 64 := Finset.mem_range.mp hn
      interval_cases n
      · norm_num [b, ArithmeticFunction.vonMangoldt_apply]
      · norm_num [b, ArithmeticFunction.vonMangoldt_apply]
      · have hv : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (14142/10000 : ℝ) ≤ Real.sqrt 2 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (17320/10000 : ℝ) ≤ Real.sqrt 3 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · have hv : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (20000/10000 : ℝ) ≤ Real.sqrt 4 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (22360/10000 : ℝ) ≤ Real.sqrt 5 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l5]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 6 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (26457/10000 : ℝ) ≤ Real.sqrt 7 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l7]
      · have hv : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (28284/10000 : ℝ) ≤ Real.sqrt 8 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (30000/10000 : ℝ) ≤ Real.sqrt 9 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 10 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 11 = Real.log 11 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (33166/10000 : ℝ) ≤ Real.sqrt 11 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l11]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 12 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 13 = Real.log 13 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (36055/10000 : ℝ) ≤ Real.sqrt 13 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l13]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 14 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 15 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (40000/10000 : ℝ) ≤ Real.sqrt 16 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 17 = Real.log 17 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (41231/10000 : ℝ) ≤ Real.sqrt 17 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l17]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 18 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 19 = Real.log 19 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (43588/10000 : ℝ) ≤ Real.sqrt 19 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l19]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 20 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 21 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 22 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 23 = Real.log 23 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (47958/10000 : ℝ) ≤ Real.sqrt 23 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l23]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 24 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 25 = Real.log 5 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (50000/10000 : ℝ) ≤ Real.sqrt 25 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l5]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 26 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 27 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (51961/10000 : ℝ) ≤ Real.sqrt 27 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 28 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 29 = Real.log 29 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (53851/10000 : ℝ) ≤ Real.sqrt 29 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l29]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 30 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 31 = Real.log 31 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (55677/10000 : ℝ) ≤ Real.sqrt 31 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l31]
      · have hv : ArithmeticFunction.vonMangoldt 32 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (56568/10000 : ℝ) ≤ Real.sqrt 32 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 33 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 34 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 35 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 36 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 37 = Real.log 37 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (60827/10000 : ℝ) ≤ Real.sqrt 37 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l37]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 38 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 39 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 40 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 41 = Real.log 41 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (64031/10000 : ℝ) ≤ Real.sqrt 41 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l41]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 42 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 43 = Real.log 43 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (65574/10000 : ℝ) ≤ Real.sqrt 43 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l43]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 44 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 45 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 46 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 47 = Real.log 47 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (68556/10000 : ℝ) ≤ Real.sqrt 47 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l47]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 48 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 49 = Real.log 7 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (70000/10000 : ℝ) ≤ Real.sqrt 49 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l7]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 50 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 51 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 52 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 53 = Real.log 53 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (72801/10000 : ℝ) ≤ Real.sqrt 53 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l53]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 54 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 55 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 56 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 57 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 58 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 59 = Real.log 59 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (76811/10000 : ℝ) ≤ Real.sqrt 59 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l59]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 60 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 61 = Real.log 61 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (78102/10000 : ℝ) ≤ Real.sqrt 61 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l61]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 62 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 63 by decide +kernel)]
        norm_num [b]
    calc _ ≤ ∑ n ∈ Finset.range 64, b n := Finset.sum_le_sum hb
         _ ≤ (288/1000 : ℝ) := by norm_num [b, Finset.sum_range_succ]
  have htail (n : ℕ) (hn : 64 ≤ n) : f n ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.fl n / 8 := by
    change ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.fl n / 8
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : (8 : ℝ) ≤ Real.sqrt n := by
      apply (Real.le_sqrt (by norm_num) hn0.le).2
      norm_num; exact_mod_cast hn
    have hp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.fl
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hn0) hp)).2
    have hv : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hh : Real.log n ≤ Real.log n * (Real.sqrt n / 8) := by nlinarith
    calc ArithmeticFunction.vonMangoldt n ≤ Real.log n := hv
         _ ≤ Real.log n * (Real.sqrt n / 8) := hh
         _ = Real.log n / (n : ℝ)^2 / 8 * ((n : ℝ)^2 * Real.sqrt n) := by field_simp
  have hgt : LeanLab.PNTPort.ExplicitPsi1.Trivial.gt 63 / 8 ≤ (11/1000 : ℝ) := by
    have hlog : Real.log 63 ≤ (21/5 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (63 : ℝ) ≤ ∑ i ∈ Finset.range 20, (21/5 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.gt
    norm_num
    linarith
  have haux (M : ℕ) (hM : 64 ≤ M) :
      ∑ n ∈ Finset.range M, f n ≤ ∑ n ∈ Finset.range 64, f n + LeanLab.PNTPort.ExplicitPsi1.Trivial.gt 63 / 8 - LeanLab.PNTPort.ExplicitPsi1.Trivial.gt ((M : ℝ) - 1) / 8 := by
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      rw [Finset.sum_range_succ]
      have hn : (4 : ℝ) ≤ M := by exact_mod_cast (by omega : 4 ≤ M)
      have htele := LeanLab.PNTPort.ExplicitPsi1.Trivial.tele_step hn
      have ht := htail M hM
      unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.fl at ht
      rw [show ((M + 1 : ℕ) : ℝ) - 1 = M by push_cast; ring]
      linarith
  have hpartial (M : ℕ) : ∑ n ∈ Finset.range M, f n ≤ (3/10 : ℝ) := by
    by_cases hM : 64 ≤ M
    · have h1 := haux M hM
      have h2 : 0 ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.gt ((M : ℝ) - 1) := LeanLab.PNTPort.ExplicitPsi1.Trivial.gt_nonneg (by
        have hMr : (64 : ℝ) ≤ M := by exact_mod_cast hM
        linarith)
      linarith
    · have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f := f)
        (Finset.range_subset_range.mpr (by omega : M ≤ 64)) (fun n _ _ => hf0 n)
      linarith
  have hsum : Summable f := summable_of_sum_range_le hf0 hpartial
  have hn (n : ℕ) : ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖ = f n := by
    rw [LSeries.norm_term_eq]
    split_ifs with hz
    · subst n; simp [f]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      norm_num
      change ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5/2 : ℝ) = f n
      rw [show (5/2 : ℝ) = 2 + 1/2 by norm_num, Real.rpow_add_of_nonneg (by positivity) (by norm_num) (by norm_num), Real.rpow_two, ← Real.sqrt_eq_rpow]
  have hsn : Summable (fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖) := hsum.congr (fun n => (hn n).symm)
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (5/2 : ℂ) + t * I) (by simp; norm_num)
  have he : logDeriv riemannZeta ((5/2 : ℂ) + t * I) = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) := by
    rw [hL, logDeriv_apply]; ring
  rw [he, norm_neg]
  calc _ ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm hsn
       _ = ∑' n, f n := tsum_congr hn
       _ ≤ 3/10 := Real.tsum_le_of_sum_range_le hf0 hpartial

set_option maxHeartbeats 200000
set_option maxRecDepth 1000

/-- LEAF. Unit U-1551. Stirling for the digamma function: `Re ψ(9/4 + iu) ≤ log|9/4 + iu| + 1/10`
for every real `u`; the float maximum of `Re ψ(9/4 + iu) - log|9/4 + iu|` over `|u| ≤ 200` is
negative, `-2.6·10⁻⁵`, and `Re ψ(z) = log|z| - Re z/(2|z|²) + O(|z|⁻²)`. -/
theorem digamma_re_le (u : ℝ) :
    (digamma ((9 / 4 : ℂ) + u * I)).re ≤ Real.log ‖(9 / 4 : ℂ) + u * I‖ + 1 / 10 := by
  sorry

/-- LEAF. Unit U-1551. The real inequality closing the bound: for `|g| ≥ 14`,
`2 (3/10 + Re 1/(3/2 + ig) - (1/2) log π + (log|9/4 + ig/2| + 1/10)/2) ≤ log |g|`; the left
side is at most `log |g| - 1.07`. -/
theorem final_numeric (g : ℝ) (hg : 14 ≤ |g|) :
    2 * (3 / 10 + (1 / ((3 / 2 : ℂ) + g * I)).re - Real.log Real.pi / 2
      + (Real.log ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ + 1 / 10) / 2) ≤ Real.log |g| := by
  have hg0 : 0 < |g| := by linarith
  have hsq : 196 ≤ g ^ 2 := by nlinarith [sq_abs g, sq_nonneg (|g| - 14)]
  have hn : ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ ≤ |g| := by
    apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith
  have hn0 : 0 < ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ := by
    apply norm_pos_iff.mpr
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hl := Real.log_le_log hn0 hn
  have hpi : 1 ≤ Real.log Real.pi := by
    exact (Real.le_log_iff_exp_le Real.pi_pos).mpr
      (Real.exp_one_lt_three.le.trans Real.pi_gt_three.le)
  have hi : (1 / ((3 / 2 : ℂ) + g * I)).re ≤ 1 / 10 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    norm_num
    apply (div_le_iff₀ (by nlinarith [sq_nonneg g] : (0 : ℝ) < 9 / 4 + g * g)).mpr
    nlinarith
  linarith

lemma re_inv_two (d : ℝ) : (1 / ((2 : ℂ) + d * I)).re = 2 / (4 + d ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp
  ring

/-- ASSEMBLY. Under RH, `HadamardK gZ`: for every finite set `s` of zeros and every zero `i`,
`Σ_{j ∈ s} 4/(4 + (γ_i - γ_j)²) ≤ log |γ_i|`. CONDITIONAL ON the leaves `xi_growth`,
`xi_zero_iff`, `logDeriv_xi`, `hadamard_re_sum_of`, `logDeriv_bound_5half`, `digamma_re_le`,
`final_numeric`, and through `Decomp1551c.ordinates14_gZ_of_RH` on the leaves of that file. -/
theorem hadamardK_gZ_of_RH (hRH : RiemannHypothesis) :
    LeanLab.ChirreHagen2025.SmoothT2.HadamardK gZ := by
  intro s i
  set g := gZ i with hg
  have h14 : 14 ≤ |g| := Decomp1551c.ordinates14_gZ_of_RH hRH i
  set z : ℂ := (5 / 2 : ℂ) + g * I with hzdef
  have hzre : 1 < z.re := by simp [hzdef]; norm_num
  have hS := hadamard_re_sum_of xi_growth xi_zero_iff logDeriv_xi z hzre
  have hrho : ∀ j : ZIdx, (j.1 : ℂ) = (1 / 2 : ℂ) + (gZ j : ℂ) * I := by
    intro j
    apply Complex.ext <;> simp [re_half_of_RH hRH j.1, gZ]
  have hterm : ∀ j : ZIdx, (1 / (z - (j.1 : ℂ))).re = K (g - gZ j) / 2 := by
    intro j
    have : z - (j.1 : ℂ) = (2 : ℂ) + ((g - gZ j : ℝ) : ℂ) * I := by
      rw [hrho j, hzdef]; push_cast; ring
    rw [this, re_inv_two]
    unfold K
    ring
  have hnn : ∀ j : ZIdx, 0 ≤ (1 / (z - (j.1 : ℂ))).re := by
    intro j; rw [hterm j]; unfold K; positivity
  have hsum := sum_le_hasSum s (fun j _ => hnn j) hS
  have hK : ∑ j ∈ s, K (g - gZ j) = 2 * ∑ j ∈ s, (1 / (z - (j.1 : ℂ))).re := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [hterm j]; ring
  have hb1 : (logDeriv ζ z).re ≤ 3 / 10 :=
    (Complex.re_le_norm _).trans (logDeriv_bound_5half g)
  have hz1 : z - 1 = (3 / 2 : ℂ) + g * I := by rw [hzdef]; ring
  have hz2 : z / 2 + 1 = (9 / 4 : ℂ) + ((g / 2 : ℝ) : ℂ) * I := by rw [hzdef]; push_cast; ring
  have hb2 := digamma_re_le (g / 2)
  have hfin := final_numeric g h14
  rw [hz1, hz2] at hsum
  rw [hK]
  linarith

end LeanLab.Routes.Decomp1551b
