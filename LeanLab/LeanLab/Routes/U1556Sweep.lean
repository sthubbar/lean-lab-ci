/-
Unit U-1556, T3 daily CONNECTION SWEEP, run 20261026T1219Z-15327, idea I-0130.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Binary Goldbach is OPEN; nothing here is progress on it. KNOWN in method.

Connection: U-1522 (I-0126) proved, from open leaves, a Goldbach number in every
`(x, x + 2.62 log² x]`, x ≥ 10^18, CONDITIONAL ON `WeightedJθ 1.0099 (10^13) (10^-13)`, a
smoothed θ mean square at one centre, and a θ error bound. The input `WeightedJθ` is supplied
by the lab's own ChirreHagen2025 chain once its Fatou step keeps the weight `W` over (2, ∞):
`SmoothY.integrableOn_P_W` and `integral_P_W_le` already hold on all of (0, ∞) with weight
`W(y/X)`, and the diagonal `HadamardK` plus `U6806.diag_u6806` gives the constant 1.0068.

* `fatou_weighted`: generic Fatou step, ANY measurable nonnegative weight. PROVED.
* `A_sq_W_le`: the weighted ψ form, `∫_{y>2} (V - B)² W(y/X) ≤ X² · B₀`, from ExplicitA,
  HadamardK and any bound `B₀` on `Σ |c_i|² log|γ_i|`. PROVED.
* `weightedJθ_of_explicit`: `U1522.WeightedJθ 1.0099 (10^13) (10^-13)` CONDITIONAL ON
  ExplicitA, HadamardK, the diagonal 1.0068 bound, and the two open leaves `bias_W_le`,
  `dqt_W_le` (the ψ to θ step with the weight kept). Real proof from them.
* `goldbach_262_all`: every `x ≥ 4` has a Goldbach number in `(x, x + 2.62 log² x]`,
  CONDITIONAL ON the same inputs, the θ bound `|θ u - u| ≤ u/10^6` for `u ≥ 10^16`, the 4·10^18
  even check, and through `U1522.goldbach_262_of_weighted` the 6 open leaves of U-1522.
The two remaining one-line links are not imported, to keep the build closure small:
`hD` is exactly `LeanLab.ChirreHagen2025.U6806.diag_u6806 hN h14` (BPTN, Ordinates14), and `hT`
is `LeanLab.ChirreHagen2025.U1348.ThetaRel6`, supplied under RH by
`LeanLab.Routes.U1505.thetaRel6_of_RH_hsw`.
-/
import Mathlib
import LeanLab.ChirreHagen2025.SmoothTheorem2
import LeanLab.Routes.U1522Frontier

namespace LeanLab.Routes.U1556

open Real MeasureTheory Set Filter Topology Chebyshev
open LeanLab.ChirreHagen2025 LeanLab.ChirreHagen2025.SmoothKernel LeanLab.ChirreHagen2025.SmoothT2
open LeanLab.ChirreHagen2025.Local36 (V)

variable {ι : Type*}

/-- U-1522's weight `Wt` is the SmoothY weight `W`. Unit U-1556. -/
theorem Wt_eq_W (r : ℝ) : U1522.Wt r = W r := rfl

/-- `y ↦ W(y/X)` is measurable. Unit U-1556. -/
theorem measurable_W_div (X : ℝ) : Measurable (fun y : ℝ => W (y / X)) := by
  unfold W
  exact Measurable.ite (measurableSet_le (measurable_id.div_const X) measurable_const)
    measurable_const ((measurable_id.div_const X).pow_const 4).inv

/-- Generic Fatou step with the weight kept: if every truncated zero sum has weighted mean
square at most `M` over `(2, ∞)`, then so does `V - B`, which is integrable there. PROVED.
Unit U-1556. -/
theorem fatou_weighted {γ : ι → ℝ} {Z : ℕ → Finset ι} {δ M : ℝ} {ω : ℝ → ℝ}
    (hω : Measurable ω) (hω0 : ∀ y, 0 ≤ ω y) (hE : ExplicitA γ Z δ) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hI : ∀ n, IntegrableOn (fun y => ‖P (Z n) (cδ γ δ) γ y‖ ^ 2 * ω y) (Ioi 2))
    (hB : ∀ n, ∫ y in Ioi 2, ‖P (Z n) (cδ γ δ) γ y‖ ^ 2 * ω y ≤ M) :
    IntegrableOn (fun y => (V δ y - Bf δ y) ^ 2 * ω y) (Ioi 2) ∧
      ∫ y in Ioi 2, (V δ y - Bf δ y) ^ 2 * ω y ≤ M := by
  set g : ℝ → ℝ := fun y => (V δ y - Bf δ y) ^ 2 * ω y with hg
  set f : ℕ → ℝ → ENNReal :=
    fun n y => ENNReal.ofReal (‖P (Z n) (cδ γ δ) γ y‖ ^ 2 * ω y) with hf
  have hn : ∀ n, ∫⁻ y in Ioi 2, f n y ≤ ENNReal.ofReal M := by
    intro n
    rw [hf, ← ofReal_integral_eq_lintegral_ofReal (hI n)
      (Filter.Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (hω0 y))]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hae : ∀ᵐ y ∂(volume.restrict (Ioi (2 : ℝ))),
      Tendsto (fun n => f n y) atTop (𝓝 (ENNReal.ofReal (g y))) := by
    have h1 : ∀ᵐ y ∂(volume.restrict (Ioi (2 : ℝ))), y ∈ Ioi (2 : ℝ) :=
      ae_restrict_mem measurableSet_Ioi
    have h2 : ∀ᵐ y ∂(volume.restrict (Ioi (2 : ℝ))), 2 ≤ y →
        Tendsto (fun n => P (Z n) (cδ γ δ) γ y) atTop (𝓝 (-((V δ y - Bf δ y : ℝ) : ℂ))) :=
      ae_restrict_of_ae hE
    filter_upwards [h1, h2] with y hy hT
    have ht := hT (le_of_lt hy)
    have hn := (continuous_norm.tendsto _).comp ht
    have hsq := ((continuous_pow 2).tendsto _).comp hn
    have hmul := hsq.mul_const (ω y)
    have hof := (ENNReal.continuous_ofReal.tendsto _).comp hmul
    have e : ‖-((V δ y - Bf δ y : ℝ) : ℂ)‖ ^ 2 * ω y = g y := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e] at hof
    exact hof
  have hmeas : ∀ n, Measurable (f n) := fun n =>
    ENNReal.measurable_ofReal.comp (((measurable_P _ _ _).norm.pow_const 2).mul hω)
  have hlim : ∫⁻ y in Ioi 2, ENNReal.ofReal (g y) ≤ ENNReal.ofReal M := by
    calc ∫⁻ y in Ioi 2, ENNReal.ofReal (g y)
        = ∫⁻ y in Ioi 2, liminf (fun n => f n y) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with y hy
          exact hy.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ y in Ioi 2, f n y) atTop := lintegral_liminf_le hmeas
      _ ≤ ENNReal.ofReal M := by
          refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
          obtain ⟨n, hn'⟩ := hb.exists
          exact hn'.trans (hn n)
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioi (2 : ℝ))) :=
    ((((measurable_V δ hδ).sub (measurable_Bf δ)).pow_const 2).mul hω).aestronglyMeasurable
  have hg0 : 0 ≤ᵐ[volume.restrict (Ioi (2 : ℝ))] g :=
    Filter.Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (hω0 y)
  have hInt : IntegrableOn g (Ioi 2) :=
    ⟨hgm, (hasFiniteIntegral_iff_ofReal hg0).mpr (lt_of_le_of_lt hlim ENNReal.ofReal_lt_top)⟩
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hg0 hgm]
  exact ENNReal.toReal_le_of_le_ofReal hM hlim

/-- The weighted ψ form at centre `X`: `∫_{y>2} (V - B)² W(y/X) ≤ X² B₀`, CONDITIONAL ON
ExplicitA and HadamardK, for any bound `B₀` on the diagonal `Σ |c_i|² log|γ_i|`. PROVED.
With `B₀ = 1.0068 δ log²(2.0001/δ)` from `U6806.diag_u6806` this is the smoothed form of
`A_sq_le_u6806` with `W` kept beyond `X`. Unit U-1556. -/
theorem A_sq_W_le {γ : ι → ℝ} {Z : ℕ → Finset ι} {δ X B₀ : ℝ} (hδ : 0 ≤ δ) (hX : 0 < X)
    (hE : ExplicitA γ Z δ) (hH : HadamardK γ)
    (hD : ∀ s : Finset ι, ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ B₀) :
    IntegrableOn (fun y => (V δ y - Bf δ y) ^ 2 * W (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, (V δ y - Bf δ y) ^ 2 * W (y / X) ≤ X ^ 2 * B₀ := by
  have hB0 : 0 ≤ B₀ := by simpa using hD ∅
  refine fatou_weighted (measurable_W_div X) (fun y => W_nonneg _) hE hδ (by positivity)
    (fun n => (integrableOn_P_W (Z n) (cδ γ δ) γ hX).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2))) (fun n => ?_)
  have hI := integrableOn_P_W (Z n) (cδ γ δ) γ hX
  have m1 : ∫ y in Ioi 2, ‖P (Z n) (cδ γ δ) γ y‖ ^ 2 * W (y / X)
      ≤ ∫ y in Ioi 0, ‖P (Z n) (cδ γ δ) γ y‖ ^ 2 * W (y / X) :=
    setIntegral_mono_set hI
      (Filter.Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (W_nonneg _))
      (Filter.Eventually.of_forall (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2)))
  have m2 := integral_P_W_le (Z n) (cδ γ δ) γ hX
  have m3 : ∑ i ∈ Z n, ‖cδ γ δ i‖ ^ 2 * ∑ j ∈ Z n, K (γ i - γ j)
      ≤ ∑ i ∈ Z n, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hH (Z n) i) (sq_nonneg _)
  have m4 := (m3.trans (hD (Z n)))
  have m5 := mul_le_mul_of_nonneg_left m4 (sq_nonneg X)
  linarith

/-- The prime power part `D(y) = (ψ - θ)((1+δ)y) - (ψ - θ)(y)`. Unit U-1556. -/
noncomputable def Dqt (δ y : ℝ) : ℝ := (ψ ((1 + δ) * y) - θ ((1 + δ) * y)) - (ψ y - θ y)

theorem Etheta_eq (δ y : ℝ) : U1522.Eθ δ y = (V δ y - Bf δ y) + Bf δ y - Dqt δ y := by
  unfold U1522.Eθ V Dqt; ring

theorem measurable_Dqt (δ : ℝ) : Measurable (Dqt δ) := by
  have hp : Measurable (fun t : ℝ => ψ t) := Chebyshev.psi_mono.measurable
  have ht : Measurable (fun t : ℝ => θ t) := Chebyshev.theta_mono.measurable
  have hl : Measurable (fun y : ℝ => (1 + δ) * y) := measurable_const.mul measurable_id
  unfold Dqt
  exact ((hp.comp hl).sub (ht.comp hl)).sub (hp.sub ht)

theorem measurable_Etheta (δ : ℝ) : Measurable (U1522.Eθ δ) := by
  have ht : Measurable (fun t : ℝ => θ t) := Chebyshev.theta_mono.measurable
  have hl : Measurable (fun y : ℝ => (1 + δ) * y) := measurable_const.mul measurable_id
  unfold U1522.Eθ
  exact ((ht.comp hl).sub ht).sub (measurable_const.mul measurable_id)

/-! ### Open leaves: the ψ to θ step with the weight kept -/

/-- LEAF. Unit U-1556. The bias term of the explicit formula, weighted: for `0 < δ ≤ 1` and
`X ≥ 2`, `B_δ(y)² W(y/X)` is integrable on `y > 2` and its integral is at most `2δ²X`.
Plain math: `B_δ(y)² ≤ δ²` for `y ≥ 2` (lab `Bf_sq_le`) and `∫_2^∞ W(y/X) dy ≤ X + X/3`. -/
theorem bias_W_le {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX : 2 ≤ X) :
    IntegrableOn (fun y => Bf δ y ^ 2 * W (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, Bf δ y ^ 2 * W (y / X) ≤ 2 * δ ^ 2 * X := by
  sorry

/-- LEAF. Unit U-1556. The prime power difference, weighted, unconditional: for
`0 < δ ≤ 10^-13` and `X ≥ 10^13`, `D(y)² W(y/X)` with `D = (ψ - θ)((1+δ)y) - (ψ - θ)(y)` is
integrable on `y > 2` and `∫_{y>2} D² W(y/X) ≤ 10^-6 δ log²(2.0001/δ) X²`.
Plain math: `D ≥ 0` is supported near prime powers `p^k`, `k ≥ 2`; when `δ√y < 1` the lab's
`Dpt_le` gives `D ≤ log²((1+δ)y)/log 2` and `∫ D W ≈ δ Σ p^k log p W(p^k/X) ≪ δ X^{3/2} log X`, so
the ratio is about `0.27 log X /(L² √X) < 10^-8` at `X = 10^13`; when `δ√y ≥ 1`,
`D ≤ θ(√((1+δ)y)) - θ(√y) + O(y^{1/3})` and Brun-Titchmarsh give `D² ≪ δ² y log² y`, ratio `≪ δ`. -/
theorem dqt_W_le {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X) :
    IntegrableOn (fun y => Dqt δ y ^ 2 * W (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, Dqt δ y ^ 2 * W (y / X)
        ≤ 1 / 10 ^ 6 * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  sorry

/-! ### Assembly -/

/-- `(u + b - d)² ≤ (501/500) u² + 1002 (b² + d²)`. PROVED. Unit U-1556. -/
theorem split3 (u b d : ℝ) : (u + b - d) ^ 2 ≤ 501 / 500 * u ^ 2 + 1002 * (b ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (u - 500 * (b - d)), sq_nonneg (b + d)]

/-- `log(2.0001/δ) ≥ 1` for `0 < δ ≤ 10^-13`. PROVED. Unit U-1556. -/
theorem L_ge_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) : 1 ≤ Real.log (2.0001 / δ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  rw [le_div_iff₀ hδ]
  nlinarith

/-- ASSEMBLY, CONDITIONAL ON the open leaves `bias_W_le` and `dqt_W_le`, and on ExplicitA,
HadamardK and the diagonal bound 1.0068 (the conclusion of `U6806.diag_u6806`): U-1522's input
`WeightedJθ 1.0099 (10^13) (10^-13)`. Constant: `(501/500)·1.0068 + 1002·10^-6 = 1.00982 < 1.0099`.
Real proof. Unit U-1556. -/
theorem weightedJθ_of_explicit {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ) (hH : HadamardK γ)
    (hD : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ∀ s : Finset ι,
      ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ 1.0068 * δ * Real.log (2.0001 / δ) ^ 2) :
    U1522.WeightedJθ 1.0099 (10 ^ 13) (1 / 10 ^ 13) := by
  intro X δ hX hδ hδ0
  have hX0 : 0 < X := by linarith
  have hδ1 : δ ≤ 1 := le_trans hδ0 (by norm_num)
  obtain ⟨iA, bA⟩ := A_sq_W_le hδ.le hX0 (hE δ hδ hδ0) hH (hD δ hδ hδ0)
  obtain ⟨iB, bB⟩ := bias_W_le (X := X) hδ hδ1 (by linarith)
  obtain ⟨iD, bD⟩ := dqt_W_le hδ hδ0 hX
  set L := Real.log (2.0001 / δ) with hL
  have hW : (fun y => U1522.Eθ δ y ^ 2 * U1522.Wt (y / X))
      = fun y => U1522.Eθ δ y ^ 2 * W (y / X) := rfl
  rw [hW]
  have hpt : ∀ y, U1522.Eθ δ y ^ 2 * W (y / X)
      ≤ 501 / 500 * ((V δ y - Bf δ y) ^ 2 * W (y / X))
        + 1002 * (Bf δ y ^ 2 * W (y / X) + Dqt δ y ^ 2 * W (y / X)) := by
    intro y
    have h := mul_le_mul_of_nonneg_right (split3 (V δ y - Bf δ y) (Bf δ y) (Dqt δ y))
      (W_nonneg (y / X))
    rw [← Etheta_eq] at h
    nlinarith [W_nonneg (y / X)]
  have iBD : IntegrableOn (fun y => Bf δ y ^ 2 * W (y / X) + Dqt δ y ^ 2 * W (y / X)) (Ioi 2) :=
    iB.add iD
  have iR : IntegrableOn (fun y => 501 / 500 * ((V δ y - Bf δ y) ^ 2 * W (y / X))
      + 1002 * (Bf δ y ^ 2 * W (y / X) + Dqt δ y ^ 2 * W (y / X))) (Ioi 2) :=
    (iA.const_mul _).add (iBD.const_mul _)
  have iE : IntegrableOn (fun y => U1522.Eθ δ y ^ 2 * W (y / X)) (Ioi 2) := by
    refine Integrable.mono' iR
      ((((measurable_Etheta δ).pow_const 2).mul (measurable_W_div X)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (W_nonneg _))]
    exact hpt y
  refine ⟨iE, ?_⟩
  have hmono : ∫ y in Ioi 2, U1522.Eθ δ y ^ 2 * W (y / X)
      ≤ ∫ y in Ioi 2, (501 / 500 * ((V δ y - Bf δ y) ^ 2 * W (y / X))
        + 1002 * (Bf δ y ^ 2 * W (y / X) + Dqt δ y ^ 2 * W (y / X))) :=
    integral_mono iE iR hpt
  rw [integral_add (iA.const_mul _) (iBD.const_mul _), integral_const_mul,
    integral_const_mul, integral_add iB iD] at hmono
  have hL1 : 1 ≤ L := L_ge_one hδ hδ0
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  -- the bias term is negligible: 2004 δ² X ≤ 10^-5 δ L² X²
  have hbias : 1002 * (2 * δ ^ 2 * X) ≤ 1 / 10 ^ 5 * δ * L ^ 2 * X ^ 2 := by
    have h1 : δ * X ≤ X * X / 10 ^ 26 := by
      have : δ * X ≤ 1 / 10 ^ 13 * X := mul_le_mul_of_nonneg_right hδ0 hX0.le
      have h2 : 1 / 10 ^ 13 * X ≤ X * X / 10 ^ 26 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith
      linarith
    have h3 : 0 ≤ δ := hδ.le
    have h4 : δ * (δ * X) ≤ δ * (X * X / 10 ^ 26) := mul_le_mul_of_nonneg_left h1 h3
    have h5 : δ * X ^ 2 ≤ δ * L ^ 2 * X ^ 2 := by
      have := mul_le_mul_of_nonneg_left hL2 (by positivity : 0 ≤ δ * X ^ 2)
      nlinarith
    nlinarith
  have hfin : 501 / 500 * (X ^ 2 * (1.0068 * δ * L ^ 2))
      + 1002 * (2 * δ ^ 2 * X + 1 / 10 ^ 6 * δ * L ^ 2 * X ^ 2)
      ≤ 1.0099 * δ * L ^ 2 * X ^ 2 := by
    have hp : 0 ≤ δ * L ^ 2 * X ^ 2 := by positivity
    nlinarith
  have hA' : 501 / 500 * ∫ y in Ioi 2, (V δ y - Bf δ y) ^ 2 * W (y / X)
      ≤ 501 / 500 * (X ^ 2 * (1.0068 * δ * L ^ 2)) :=
    mul_le_mul_of_nonneg_left bA (by norm_num)
  linarith

/-- HEADLINE, CONDITIONAL ON ExplicitA, HadamardK, the diagonal bound 1.0068 (all three as
in `theorem2_u6806`, which encode RH through the explicit formula along critical line
ordinates), `|θ u - u| ≤ u/10^6` for `u ≥ 10^16` (U1348 `ThetaRel6`, under RH by
`U1505.thetaRel6_of_RH_hsw`), the 4·10^18 even check, the open leaves `bias_W_le`, `dqt_W_le`
here and the 6 open leaves of U-1522: for every `x ≥ 4` a sum of two odd primes lies in
`(x, x + 2.62 log² x]`. Real proof. Unit U-1556. -/
theorem goldbach_262_all {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ) (hH : HadamardK γ)
    (hD : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ∀ s : Finset ι,
      ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ 1.0068 * δ * Real.log (2.0001 / δ) ^ 2)
    (hT : ∀ u : ℝ, 10 ^ 16 ≤ u → |θ u - u| ≤ u / 10 ^ 6)
    (hEv : LeanLab.EvenGoldbachUpTo (4 * 10 ^ 18)) {x : ℝ} (hx : 4 ≤ x) :
    U1522.GoldbachIn x (x + 2.62 * Real.log x ^ 2) := by
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, ⟨p, q, hp, hq, hpo, hqo, hpq⟩, h1, h2⟩ := small_of hEv x (by linarith) hs
    have hlog : 1.3 ≤ Real.log x := by
      have h4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
      have h22 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      linarith
    refine ⟨p, q, hp, hq, hpo, hqo, ?_, ?_⟩
    · rw [hpq]; exact h1
    · rw [hpq]; nlinarith
  · exact U1522.goldbach_262_of_weighted (weightedJθ_of_explicit hE hH hD) hT (by linarith)

/-- Vacuity instance for `split3`, a concrete case with every term positive:
`u = b = d = 1`, `1 ≤ 501/500 + 2004`. Unit U-1556. -/
theorem split3_vacuity : ((1 : ℝ) + 1 - 1) ^ 2 ≤ 501 / 500 * 1 ^ 2 + 1002 * (1 ^ 2 + 1 ^ 2) :=
  split3 1 1 1

end LeanLab.Routes.U1556
