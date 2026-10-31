/-
Unit U-1556, T3 daily CONNECTION SWEEP, run 20261026T1219Z-15327, idea I-0131.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Binary Goldbach is OPEN; nothing here is progress on it. KNOWN in method.

Connection: the exponent 4 in U-1522's weight `W(u) = min(1, u^-4)` is not forced. For
`w_a(v) = exp(-a|v|)`, `y = X e^v`, the weight is `W_a(u) = u^(a-2)` for `u ≤ 1` and
`u^(-2-a)` for `u > 1`, its kernel is `K_a(t) = 2a/(a² + t²)` (a = 2 is the lab's `K`), and
by the Hadamard product `Σ_ρ K_a(γ - γ_ρ) = 2 Re ξ'/ξ(1/2 + a + iγ) ≤ log(|γ|/2π) + 2(-ζ'/ζ)(1/2 + a)`
up to `O(1/γ²)`, which is at most `log|γ|` as soon as `a ≥ a* = 1.22307`
(`2(-ζ'/ζ)(1.723) = log 2π`). So for `a = 3/2` the lab's diagonal chain, HadamardK followed by
`U6806.diag_u6806`, gives the SAME constant 1.0068, while the AM-GM pairing of U-1522 at the
centre x/2 gains: `κ(a) = 1/(2 ∫_0^{1/2} (s/(1-s))^{a/2} ds)`, 2.5887 at a = 2, 2.1622 at
a = 3/2, 1.9327 at a*. Numerics: Routes/numerics/U1556/.

* `HadamardKa`, `WeightedJθa`: new Props, vacuity instances PROVED.
* `A_sq_Wa_le`: the weighted ψ form for `W_a`, CONDITIONAL ON leaves `integrableOn_P_Wa`,
  `integral_P_Wa_le` (SmoothY with `w_a` in place of `e^{-2|v|}`), ExplicitA, HadamardKa.
* `weightedJθa_of_explicit`: `WeightedJθa (3/2) 1.0099 (10^13) (10^-13)`, from leaves.
* `goldbach_of_weighted_a`, `goldbach_219_of_weighted_a`: the pairing with `U_a`, real
  proofs from leaves, gives `(x, x + 2.19 log² x]` for `x ≥ 10^18`.
* `goldbach_219_all`: every `x ≥ 4`, CONDITIONAL ON the named inputs and the leaves.
-/
import Mathlib
import LeanLab.Routes.U1556Sweep

namespace LeanLab.Routes.U1556B

open Real MeasureTheory Set Filter Topology Chebyshev
open LeanLab.ChirreHagen2025 LeanLab.ChirreHagen2025.SmoothKernel LeanLab.ChirreHagen2025.SmoothT2
open LeanLab.ChirreHagen2025.Local36 (V)
open LeanLab.Routes.U1556 (fatou_weighted Dqt Etheta_eq measurable_Dqt measurable_Etheta split3
  L_ge_one)

variable {ι : Type*}

/-- `K_a(t) = 2a/(a² + t²)`, the Fourier transform of `exp(-a|v|)`. Unit U-1556. -/
noncomputable def Ka (a t : ℝ) : ℝ := 2 * a / (a ^ 2 + t ^ 2)

/-- `W_a(u) = |u|^(a-2)` for `u ≤ 1`, `u^(-2-a)` for `u > 1`; used at `u > 0`. Unit U-1556. -/
noncomputable def Wa (a u : ℝ) : ℝ := if u ≤ 1 then |u| ^ (a - 2) else u ^ (-2 - a)

theorem Wa_nonneg (a u : ℝ) : 0 ≤ Wa a u := by
  unfold Wa; split_ifs with h
  · exact Real.rpow_nonneg (abs_nonneg u) _
  · exact Real.rpow_nonneg (by linarith) _

theorem measurable_Wa_div (a X : ℝ) : Measurable (fun y : ℝ => Wa a (y / X)) := by
  unfold Wa
  exact Measurable.ite (measurableSet_le (measurable_id.div_const X) measurable_const)
    ((measurable_id.div_const X).abs.pow_const _) ((measurable_id.div_const X).pow_const _)

/-- CONDITIONAL INPUT, named, the analogue of the lab's `HadamardK` for `K_a`: over every finite
set of ordinates, `Σ_j K_a(γ_i - γ_j) ≤ log |γ_i|`. For the zeros of ζ on the critical line with
`|γ| ≥ 14` it follows from the Hadamard product, `-ζ'/ζ(1/2 + a)` and `a ≥ 1.22307`; at
`a = 3/2` the margin is 0.698. Unit U-1556. -/
def HadamardKa (a : ℝ) (γ : ι → ℝ) : Prop :=
  ∀ (s : Finset ι) (i : ι), ∑ j ∈ s, Ka a (γ i - γ j) ≤ Real.log |γ i|

/-- Vacuity of `HadamardKa (3/2)`: one ordinate at 14, `K_{3/2}(0) = 4/3 ≤ log 14`. PROVED.
Unit U-1556. -/
theorem hadamardKa_vacuity : HadamardKa (3 / 2) (fun _ : Unit => (14 : ℝ)) := by
  intro s i
  have hK : Ka (3 / 2) ((14 : ℝ) - 14) = 4 / 3 := by unfold Ka; norm_num
  have hle : ∑ j ∈ s, Ka (3 / 2) ((fun _ : Unit => (14 : ℝ)) i - (fun _ : Unit => (14 : ℝ)) j)
      ≤ ∑ j ∈ (Finset.univ : Finset Unit), Ka (3 / 2) ((14 : ℝ) - 14) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro j _ _; unfold Ka; norm_num
  have hu : ∑ j ∈ (Finset.univ : Finset Unit), Ka (3 / 2) ((14 : ℝ) - 14) = 4 / 3 := by
    rw [hK]; simp
  have hlog : (4 : ℝ) / 3 ≤ Real.log |(14 : ℝ)| := by
    rw [abs_of_pos (by norm_num), Real.le_log_iff_exp_le (by norm_num)]
    have he := Real.exp_one_lt_d9
    have h2 : Real.exp (4 / 3) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h4 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  linarith

/-! ### Open leaves: SmoothY for the weight `w_a` -/

/-- LEAF. Unit U-1556. SmoothY `integrableOn_P_W` for `w_a`: for `a > 0`, `x > 0` and a finite
sum `P(y) = Σ_i c_i y^{1/2 + iγ_i}`, `|P(y)|² W_a(y/x)` is integrable on `y > 0`.
Plain math: `|P(y)|² ≪ y`, and `y · y^{a-2}` near 0, `y · y^{-2-a}` near ∞ are integrable. -/
theorem integrableOn_P_Wa {a : ℝ} (ha : 0 < a) (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ}
    (hx : 0 < x) : IntegrableOn (fun y => ‖P s c γ y‖ ^ 2 * Wa a (y / x)) (Ioi 0) := by
  sorry

/-- LEAF. Unit U-1556. SmoothY `integral_P_W_le` for `w_a`: for `a > 0`, `x > 0`,
`∫_0^∞ |P(y)|² W_a(y/x) dy ≤ x² Σ_i |c_i|² Σ_j 2a/(a² + (γ_i - γ_j)²)`.
Plain math: `y = x e^v` turns the left side into `x² ∫ |Σ_i c_i x^{iγ_i} e^{iγ_i v}|² e^{-a|v|} dv`;
expand, the Fourier transform of `e^{-a|v|}` is `K_a ≥ 0`, and `|b_i b_j| ≤ (|b_i|² + |b_j|²)/2`. -/
theorem integral_P_Wa_le {a : ℝ} (ha : 0 < a) (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ}
    (hx : 0 < x) :
    ∫ y in Ioi 0, ‖P s c γ y‖ ^ 2 * Wa a (y / x)
      ≤ x ^ 2 * ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, Ka a (γ i - γ j) := by
  sorry

/-- The weighted ψ form for `W_a`, CONDITIONAL ON the two leaves above, ExplicitA and
`HadamardKa a`, for any bound `B₀` on `Σ |c_i|² log|γ_i|`. Real proof via `fatou_weighted`.
Unit U-1556. -/
theorem A_sq_Wa_le {a : ℝ} (ha : 0 < a) {γ : ι → ℝ} {Z : ℕ → Finset ι} {δ X B₀ : ℝ}
    (hδ : 0 ≤ δ) (hX : 0 < X) (hE : ExplicitA γ Z δ) (hH : HadamardKa a γ)
    (hD : ∀ s : Finset ι, ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ B₀) :
    IntegrableOn (fun y => (V δ y - Bf δ y) ^ 2 * Wa a (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, (V δ y - Bf δ y) ^ 2 * Wa a (y / X) ≤ X ^ 2 * B₀ := by
  have hB0 : 0 ≤ B₀ := by simpa using hD ∅
  refine fatou_weighted (measurable_Wa_div a X) (fun y => Wa_nonneg _ _) hE hδ (by positivity)
    (fun n => (integrableOn_P_Wa ha (Z n) (cδ γ δ) γ hX).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2))) (fun n => ?_)
  have hI := integrableOn_P_Wa ha (Z n) (cδ γ δ) γ hX
  have m1 : ∫ y in Ioi 2, ‖P (Z n) (cδ γ δ) γ y‖ ^ 2 * Wa a (y / X)
      ≤ ∫ y in Ioi 0, ‖P (Z n) (cδ γ δ) γ y‖ ^ 2 * Wa a (y / X) :=
    setIntegral_mono_set hI
      (Filter.Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (Wa_nonneg _ _))
      (Filter.Eventually.of_forall (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2)))
  have m2 := integral_P_Wa_le ha (Z n) (cδ γ δ) γ hX
  have m3 : ∑ i ∈ Z n, ‖cδ γ δ i‖ ^ 2 * ∑ j ∈ Z n, Ka a (γ i - γ j)
      ≤ ∑ i ∈ Z n, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hH (Z n) i) (sq_nonneg _)
  have m5 := mul_le_mul_of_nonneg_left (m3.trans (hD (Z n))) (sq_nonneg X)
  linarith

/-! ### Open leaves: the ψ to θ step for `W_{3/2}` -/

/-- LEAF. Unit U-1556. For `0 < δ ≤ 1`, `X ≥ 2`: `B_δ(y)² W_{3/2}(y/X)` is integrable on `y > 2`
with integral at most `3δ²X`. Plain math: `B_δ² ≤ δ²` for `y ≥ 2` (lab `Bf_sq_le`), and
`∫_0^X (y/X)^{-1/2} dy + ∫_X^∞ (y/X)^{-7/2} dy = 2X + X/2.5`. -/
theorem bias_Wa_le {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX : 2 ≤ X) :
    IntegrableOn (fun y => Bf δ y ^ 2 * Wa (3 / 2) (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, Bf δ y ^ 2 * Wa (3 / 2) (y / X) ≤ 3 * δ ^ 2 * X := by
  sorry

/-- LEAF. Unit U-1556. Unconditional: for `0 < δ ≤ 10^-13`, `X ≥ 10^13`, with
`D = (ψ - θ)((1+δ)y) - (ψ - θ)(y)`, `D² W_{3/2}(y/X)` is integrable on `y > 2` and its integral
is at most `10^-6 δ log²(2.0001/δ) X²`. Plain math: as `U1556.dqt_W_le`; the heavier weight
`(X/y)^{1/2}` below `X` turns the prime square sum into `δ √X Σ_{p ≤ √X} p log² p ≪ δ X^{3/2} log X`. -/
theorem dqt_Wa_le {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X) :
    IntegrableOn (fun y => Dqt δ y ^ 2 * Wa (3 / 2) (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, Dqt δ y ^ 2 * Wa (3 / 2) (y / X)
        ≤ 1 / 10 ^ 6 * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  sorry

/-- CONDITIONAL INPUT, named: the θ mean square with weight `W_a` at every centre `X ≥ X0`.
`WeightedJθa 2` is U-1522's `WeightedJθ`. Unit U-1556. -/
def WeightedJθa (a c X0 δ0 : ℝ) : Prop :=
  ∀ X δ : ℝ, X0 ≤ X → 0 < δ → δ ≤ δ0 →
    IntegrableOn (fun y => U1522.Eθ δ y ^ 2 * Wa a (y / X)) (Ioi 2) ∧
    ∫ y in Ioi 2, U1522.Eθ δ y ^ 2 * Wa a (y / X) ≤ c * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2

/-- Vacuity of `WeightedJθa`, degenerate: with `δ0 = 0` no `δ` is admitted. PROVED. The
non-degenerate instance is `weightedJθa_of_explicit`, CONDITIONAL. Unit U-1556. -/
theorem weightedJθa_vacuity : WeightedJθa (3 / 2) 1.0099 (10 ^ 13) 0 := by
  intro X δ _ hδ hδ0; exact absurd hδ (not_lt.mpr hδ0)

/-- ASSEMBLY, CONDITIONAL ON the leaves `integrableOn_P_Wa`, `integral_P_Wa_le`, `bias_Wa_le`,
`dqt_Wa_le`, on ExplicitA, `HadamardKa (3/2)` and the diagonal 1.0068 bound:
`WeightedJθa (3/2) 1.0099 (10^13) (10^-13)`. Real proof. Unit U-1556. -/
theorem weightedJθa_of_explicit {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ) (hH : HadamardKa (3 / 2) γ)
    (hD : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ∀ s : Finset ι,
      ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ 1.0068 * δ * Real.log (2.0001 / δ) ^ 2) :
    WeightedJθa (3 / 2) 1.0099 (10 ^ 13) (1 / 10 ^ 13) := by
  intro X δ hX hδ hδ0
  have hX0 : 0 < X := by linarith
  have hδ1 : δ ≤ 1 := le_trans hδ0 (by norm_num)
  obtain ⟨iA, bA⟩ := A_sq_Wa_le (by norm_num) hδ.le hX0 (hE δ hδ hδ0) hH (hD δ hδ hδ0)
  obtain ⟨iB, bB⟩ := bias_Wa_le (X := X) hδ hδ1 (by linarith)
  obtain ⟨iD, bD⟩ := dqt_Wa_le hδ hδ0 hX
  set L := Real.log (2.0001 / δ) with hL
  set ω : ℝ → ℝ := fun y => Wa (3 / 2) (y / X) with hω
  have hpt : ∀ y, U1522.Eθ δ y ^ 2 * ω y
      ≤ 501 / 500 * ((V δ y - Bf δ y) ^ 2 * ω y)
        + 1002 * (Bf δ y ^ 2 * ω y + Dqt δ y ^ 2 * ω y) := by
    intro y
    have h := mul_le_mul_of_nonneg_right (split3 (V δ y - Bf δ y) (Bf δ y) (Dqt δ y))
      (Wa_nonneg (3 / 2) (y / X))
    rw [← Etheta_eq] at h
    nlinarith [Wa_nonneg (3 / 2) (y / X)]
  have iBD : IntegrableOn (fun y => Bf δ y ^ 2 * ω y + Dqt δ y ^ 2 * ω y) (Ioi 2) :=
    iB.add iD
  have iR : IntegrableOn (fun y => 501 / 500 * ((V δ y - Bf δ y) ^ 2 * ω y)
      + 1002 * (Bf δ y ^ 2 * ω y + Dqt δ y ^ 2 * ω y)) (Ioi 2) :=
    (iA.const_mul _).add (iBD.const_mul _)
  have iE : IntegrableOn (fun y => U1522.Eθ δ y ^ 2 * ω y) (Ioi 2) := by
    refine Integrable.mono' iR
      ((((measurable_Etheta δ).pow_const 2).mul (measurable_Wa_div _ X)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Wa_nonneg _ _))]
    exact hpt y
  refine ⟨iE, ?_⟩
  have hmono := integral_mono iE iR hpt
  rw [integral_add (iA.const_mul _) (iBD.const_mul _), integral_const_mul,
    integral_const_mul, integral_add iB iD] at hmono
  have hL1 : 1 ≤ L := L_ge_one hδ hδ0
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hbias : 1002 * (3 * δ ^ 2 * X) ≤ 1 / 10 ^ 5 * δ * L ^ 2 * X ^ 2 := by
    have h1 : δ * X ≤ X * X / 10 ^ 26 := by
      have : δ * X ≤ 1 / 10 ^ 13 * X := mul_le_mul_of_nonneg_right hδ0 hX0.le
      have h2 : 1 / 10 ^ 13 * X ≤ X * X / 10 ^ 26 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith
      linarith
    have h4 : δ * (δ * X) ≤ δ * (X * X / 10 ^ 26) := mul_le_mul_of_nonneg_left h1 hδ.le
    have h5 : δ * X ^ 2 ≤ δ * L ^ 2 * X ^ 2 := by
      have := mul_le_mul_of_nonneg_left hL2 (by positivity : 0 ≤ δ * X ^ 2)
      nlinarith
    nlinarith
  have hfin : 501 / 500 * (X ^ 2 * (1.0068 * δ * L ^ 2))
      + 1002 * (3 * δ ^ 2 * X + 1 / 10 ^ 6 * δ * L ^ 2 * X ^ 2)
      ≤ 1.0099 * δ * L ^ 2 * X ^ 2 := by
    have hp : 0 ≤ δ * L ^ 2 * X ^ 2 := by positivity
    nlinarith
  have hA' : 501 / 500 * ∫ y in Ioi 2, (V δ y - Bf δ y) ^ 2 * ω y
      ≤ 501 / 500 * (X ^ 2 * (1.0068 * δ * L ^ 2)) :=
    mul_le_mul_of_nonneg_left bA (by norm_num)
  linarith

/-! ### The pairing with `U_a(s) = √(W_a(2s) W_a(2(1-s)))`, `a = 3/2` -/

/-- The pairing weight for `a = 3/2`. Unit U-1556. -/
noncomputable def Ua (s : ℝ) : ℝ := Real.sqrt (Wa (3 / 2) (2 * s) * Wa (3 / 2) (2 * (1 - s)))

/-- The cross term `δ ∫ U_a(t/x) (t E(x-t) + (x-t) E(t)) dt` over `[x/64, 63x/64]`. Unit U-1556. -/

lemma Ua_nonneg (s : ℝ) : 0 ≤ Ua s := Real.sqrt_nonneg _


lemma Ua_sq (s : ℝ) : Ua s ^ 2 = Wa (3/2) (2*s) * Wa (3/2) (2*(1-s)) := by
  have Wa_nonneg : ∀ (a u : ℝ), 0 ≤ Wa a u := by
    intro a u
    unfold Wa; split_ifs with h
    · exact Real.rpow_nonneg (abs_nonneg u) _
    · exact Real.rpow_nonneg (by linarith) _
  unfold Ua
  exact Real.sq_sqrt (mul_nonneg (Wa_nonneg _ _) (Wa_nonneg _ _))

lemma continuous_Wa_pos : ContinuousOn (Wa (3/2)) (Set.Ici (1/64 : ℝ)) := by

  have hc1 : ContinuousOn (fun u : ℝ => u ^ (-1/2 : ℝ)) (Set.Ici (1/64 : ℝ)) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.rpow
    · exact continuousAt_id
    · exact continuousAt_const
    · left; exact ne_of_gt (lt_of_lt_of_le (show (0 : ℝ) < (1/64 : ℝ) by norm_num) hx)
  have hc2 : ContinuousOn (fun u : ℝ => u ^ (-7/2 : ℝ)) (Set.Ici (1/64 : ℝ)) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.rpow
    · exact continuousAt_id
    · exact continuousAt_const
    · left; exact ne_of_gt (lt_of_lt_of_le (show (0 : ℝ) < (1/64 : ℝ) by norm_num) hx)
  have h_eq : ∀ u ∈ Set.Ici (1/64 : ℝ), Wa (3/2) u = if u ≤ 1 then u ^ (-1/2 : ℝ) else u ^ (-7/2 : ℝ) := by
    intro u hu
    unfold Wa
    have h1 : (3/2 : ℝ) - 2 = -1/2 := by norm_num
    have h2 : -2 - (3/2 : ℝ) = -7/2 := by norm_num
    rw [h1, h2]
    split_ifs with h3
    · have hu_pos : 0 ≤ u := le_of_lt (lt_of_lt_of_le (show (0 : ℝ) < 1/64 by norm_num) hu)
      rw [abs_of_nonneg hu_pos]
    · rfl
  apply ContinuousOn.congr _ h_eq
  have h_eq2 : (fun u : ℝ => if u ≤ 1 then u ^ (-1/2 : ℝ) else u ^ (-7/2 : ℝ)) = Set.piecewise (Set.Iic 1) (fun u : ℝ => u ^ (-1/2 : ℝ)) (fun u : ℝ => u ^ (-7/2 : ℝ)) := by
    ext x
    unfold Set.piecewise
    simp
  rw [h_eq2]
  apply ContinuousOn.piecewise
  · intro a ha
    simp only [Set.mem_inter_iff, Set.mem_Ici, frontier_Iic, Set.mem_singleton_iff] at ha
    have ha2 : a = 1 := ha.2
    subst ha2
    norm_num
  · exact hc1.mono (fun _ hx => hx.1)
  · exact hc2.mono (fun _ hx => hx.1)

lemma continuous_Ua_interval : ContinuousOn Ua (Set.Icc (1/64 : ℝ) (63/64 : ℝ)) := by
  have hc1 : ContinuousOn (fun s => 2 * s) (Set.Icc (1/64 : ℝ) (63/64 : ℝ)) := by
    apply Continuous.continuousOn
    fun_prop
  have hc2 : ContinuousOn (fun s => 2 * (1 - s)) (Set.Icc (1/64 : ℝ) (63/64 : ℝ)) := by
    apply Continuous.continuousOn
    fun_prop
  have hc3 : ContinuousOn (fun s => Wa (3/2) (2 * s)) (Set.Icc (1/64 : ℝ) (63/64 : ℝ)) := by
    apply ContinuousOn.comp continuous_Wa_pos hc1
    intro x hx
    simp only [Set.mem_Icc, Set.mem_Ici] at hx ⊢
    linarith [hx.1]
  have hc4 : ContinuousOn (fun s => Wa (3/2) (2 * (1 - s))) (Set.Icc (1/64 : ℝ) (63/64 : ℝ)) := by
    apply ContinuousOn.comp continuous_Wa_pos hc2
    intro x hx
    simp only [Set.mem_Icc, Set.mem_Ici] at hx ⊢
    linarith [hx.2]
  have hc5 : ContinuousOn (fun s => Wa (3/2) (2 * s) * Wa (3/2) (2 * (1 - s))) (Set.Icc (1/64 : ℝ) (63/64 : ℝ)) := by
    exact hc3.mul hc4
  exact hc5.sqrt


noncomputable def crossTa (x δ : ℝ) : ℝ :=
  δ * ∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t)

/-- LEAF. Unit U-1556. As U-1522 `pairing_expand` with `U_a` in place of `U`: if
`A(t)A(x-t) = 0` on `[x/64, 63x/64]` then `δ² ∫ U_a t(x-t) + cross + ∫ U_a E(t)E(x-t) = 0`. -/
theorem pairing_expand_a {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hz : ∀ t ∈ Icc (x / 64) (63 * x / 64), U1522.Aθ δ t * U1522.Aθ δ (x - t) = 0) :
    δ ^ 2 * (∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (t * (x - t))) + crossTa x δ
      + ∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (U1522.Eθ δ t * U1522.Eθ δ (x - t)) = 0 := by
  let a := x / 64
  let b := 63 * x / 64
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have iE : ∀ c d, IntervalIntegrable (U1522.Eθ δ) volume c d := by
    intro c d
    exact LeanLab.ChirreHagen2025.Eθ_ii hδ c d
  have iEr : IntervalIntegrable (fun t => U1522.Eθ δ (x - t)) volume a b := by
    simpa only [sub_sub_cancel] using (iE (x - a) (x - b)).comp_sub_left x
  have hU : ContinuousOn (fun t => Ua (t / x)) (Set.Icc a b) := by
    have hc_id : ContinuousOn (fun t => t / x) (Set.Icc a b) := by
      apply Continuous.continuousOn
      fun_prop
    have hz_bound : ∀ t ∈ Set.Icc a b, t / x ∈ Set.Icc (1/64 : ℝ) (63/64 : ℝ) := by
      intro t ht
      dsimp [a, b] at ht
      constructor
      · exact (div_le_div_iff₀ (by norm_num) hx).mpr (by linarith [ht.1])
      · exact (div_le_div_iff₀ hx (by norm_num)).mpr (by linarith [ht.2])
    exact continuous_Ua_interval.comp hc_id hz_bound
  have hM : ContinuousOn (fun t => Ua (t / x) * (t * (x - t))) (Set.Icc a b) := by
    apply ContinuousOn.mul hU
    apply Continuous.continuousOn
    fun_prop
  have iM : IntervalIntegrable (fun t => Ua (t / x) * (t * (x - t))) volume a b := (ContinuousOn.intervalIntegrable_of_Icc hab hM)
  have iC : IntervalIntegrable
      (fun t => Ua (t / x) * (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t)) volume a b := by
    have i1 : IntervalIntegrable (fun t => Ua (t / x) * t * U1522.Eθ δ (x - t)) volume a b := by
      have hc_id : ContinuousOn (fun t : ℝ => Ua (t / x) * t) (Set.uIcc a b) := by rw [Set.uIcc_of_le hab]; exact hU.mul continuous_id.continuousOn
      exact iEr.continuousOn_mul hc_id
    have hV : ContinuousOn (fun t : ℝ => Ua (t / x) * (x - t)) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      apply hU.mul
      apply Continuous.continuousOn
      fun_prop
    have i2 := (iE a b).continuousOn_mul hV
    convert i1.add i2 using 1 <;> ext t <;> ring
  have he : ∀ t ∈ Set.uIcc a b,
      Ua (t / x) * (U1522.Eθ δ t * U1522.Eθ δ (x - t)) =
      -(δ ^ 2 * (Ua (t / x) * (t * (x - t))) +
        δ * (Ua (t / x) * (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t))) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hz' := hz t ht
    have hA : ∀ y, U1522.Aθ δ y = δ * y + U1522.Eθ δ y := by intro y; unfold U1522.Aθ U1522.Eθ; ring
    rw [hA, hA] at hz'
    have he0 := congrArg (fun z : ℝ => Ua (t / x) * z) hz'
    nlinarith only [he0]
  change δ ^ 2 * (∫ t in a..b, Ua (t / x) * (t * (x - t))) +
    δ * (∫ t in a..b, Ua (t / x) * (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t)) +
    (∫ t in a..b, Ua (t / x) * (U1522.Eθ δ t * U1522.Eθ δ (x - t))) = 0
  rw [intervalIntegral.integral_congr he, intervalIntegral.integral_neg,
    intervalIntegral.integral_add (iM.const_mul _) (iC.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring


/-- LEAF. Unit U-1556. As U-1522 `ee_le_weighted`: by `U1522.gm_split` with
`F₁ = W_a(2t/x)`, `F₂ = W_a(2(x-t)/x)` and reflection, the bilinear term is at most one weighted
mean square at the centre `x/2`. -/
theorem ee_le_weighted_a {x δ : ℝ} (hx : 128 ≤ x) (hδ : 0 < δ)
    (hint : IntegrableOn (fun y => U1522.Eθ δ y ^ 2 * Wa (3 / 2) (y / (x / 2))) (Ioi 2)) :
    |∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (U1522.Eθ δ t * U1522.Eθ δ (x - t))|
      ≤ ∫ y in Ioi 2, U1522.Eθ δ y ^ 2 * Wa (3 / 2) (y / (x / 2)) := by
  have hx0 : x ≠ 0 := by linarith
  let a := x / 64
  let b := 63 * x / 64
  let f : ℝ → ℝ := fun y => U1522.Eθ δ y ^ 2 * Wa (3 / 2) (y / (x / 2))
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have hxa : x - a = b := by dsimp [a, b]; ring
  have hxb : x - b = a := by dsimp [a, b]; ring
  have hf : IntegrableOn f (Ioi 2) := hint
  have ifab : IntervalIntegrable f volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    apply hf.mono_set
    intro t ht
    exact lt_of_le_of_lt ha ht.1
  have ifr : IntervalIntegrable (fun t => f (x - t)) volume a b := by
    simpa only [hxa, hxb, sub_sub_cancel] using ifab.symm.comp_sub_left x
  have iG : IntervalIntegrable (fun t => (f t + f (x - t)) / 2) volume a b :=
    (ifab.add ifr).div_const 2
  have hbnd : |∫ t in a..b, Ua (t / x) * (U1522.Eθ δ t * U1522.Eθ δ (x - t))| ≤
      ∫ t in a..b, (f t + f (x - t)) / 2 := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ iG
    filter_upwards [] with t ht
    have hU0 : 0 ≤ Ua (t / x) := Ua_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0]
    have hgm := U1522.gm_split hU0
      (Wa_nonneg _ _) (Wa_nonneg _ _)
      (le_of_eq (Ua_sq (t / x))) (a := U1522.Eθ δ t) (b := U1522.Eθ δ (x - t))
    have harg1 : t / (x / 2) = 2 * (t / x) := by field_simp <;> ring
    have harg2 : (x - t) / (x / 2) = 2 * (1 - t / x) := by field_simp <;> ring
    change Ua (t / x) * |U1522.Eθ δ t * U1522.Eθ δ (x - t)| ≤
      (U1522.Eθ δ t ^ 2 * Wa (3 / 2) (t / (x / 2)) + U1522.Eθ δ (x - t) ^ 2 * Wa (3 / 2) ((x - t) / (x / 2))) / 2
    rw [harg1, harg2]
    nlinarith only [hgm]
  have hreflect : (∫ t in a..b, f (x - t)) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_comp_sub_left, hxb, hxa]
  have heq : (∫ t in a..b, (f t + f (x - t)) / 2) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add ifab ifr, hreflect]
    ring
  rw [heq] at hbnd
  apply hbnd.trans
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set hf
  · exact Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (Wa_nonneg _ _))
  · exact Filter.Eventually.of_forall (fun t ht => lt_of_le_of_lt ha ht.1)


/-- LEAF. Unit U-1556. As U-1522 `cross_le` with `U_a`: with `|θ(u) - u| ≤ ηu` for `u ≥ x/64`,
`|cross| ≤ 4ηδ²x³`. -/
theorem cross_le_a {x δ η : ℝ} (hx : 128 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η)
    (hR : ∀ u : ℝ, x / 64 ≤ u → |θ u - u| ≤ η * u) :
    |crossTa x δ| ≤ 4 * η * δ ^ 2 * x ^ 3 := by
  sorry


/-- LEAF. Unit U-1556. The truncated main term for `a = 3/2`:
`∫_{x/64}^{63x/64} U_a(t/x) t(x-t) dt ≥ 0.1154 x³`. Plain math: `U_a(s) s(1-s) = (s/(1-s))^{3/4}/4`
for `s ≤ 1/2`, symmetric, and `2 ∫_{1/64}^{1/2} (s/(1-s))^{3/4}/4 ds = 0.115423`
(numerics/U1556/kernel_family_output.txt). -/
theorem main_ge_a {x : ℝ} (hx : 0 < x) :
    0.1154 * x ^ 3 ≤ ∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (t * (x - t)) := by
  sorry

/-- ASSEMBLY, CONDITIONAL ON `WeightedJθa (3/2) c X0 δ0`, `|θ u - u| ≤ ηu` for `u ≥ x/64` with
`η ≤ 10^-6`, and the leaves `pairing_expand_a`, `ee_le_weighted_a`, `cross_le_a`, `main_ge_a`
and U-1522 `goldbach_of_pair_ne`: if `2.167 c log²(2.0001/δ) < δx` then `(x, x + δx]` holds a
Goldbach number. Real proof. Unit U-1556. -/
theorem goldbach_of_weighted_a {c X0 δ0 η x δ : ℝ} (hW : WeightedJθa (3 / 2) c X0 δ0)
    (hc : 0 ≤ c) (hR : ∀ u : ℝ, x / 64 ≤ u → |θ u - u| ≤ η * u) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 10 ^ 6) (hX : X0 ≤ x / 2) (hx : 128 ≤ x) (hδ : 0 < δ) (hδ0 : δ ≤ δ0)
    (hδ1 : δ ≤ 1) (hbig : 2.167 * c * Real.log (2.0001 / δ) ^ 2 < δ * x) :
    U1522.GoldbachIn x (x + δ * x) := by
  by_contra hG
  have hz : ∀ t ∈ Icc (x / 64) (63 * x / 64), U1522.Aθ δ t * U1522.Aθ δ (x - t) = 0 := by
    intro t ht
    by_contra hne
    rcases mul_ne_zero_iff.mp hne with ⟨h1, h2⟩
    exact hG (U1522.goldbach_of_pair_ne hδ (by linarith [ht.1]) (by linarith [ht.2]) h1 h2)
  obtain ⟨hint, hJ⟩ := hW (x / 2) δ hX hδ hδ0
  have hx0 : 0 < x := by linarith
  have e := pairing_expand_a hx0 hδ hz
  have b2 := ee_le_weighted_a hx hδ hint
  have b3 := cross_le_a hx hδ hδ1 hη0 hR
  have d := main_ge_a hx0
  set I := ∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (t * (x - t)) with hI
  set C := crossTa x δ with hC
  set EE := ∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (U1522.Eθ δ t * U1522.Eθ δ (x - t))
    with hEE
  set S := ∫ y in Ioi 2, U1522.Eθ δ y ^ 2 * Wa (3 / 2) (y / (x / 2)) with hS
  set L := Real.log (2.0001 / δ) with hL
  have nC := neg_abs_le C
  have nE := neg_abs_le EE
  have hd2 : δ ^ 2 * (0.1154 * x ^ 3) ≤ δ ^ 2 * I := mul_le_mul_of_nonneg_left d (sq_nonneg δ)
  have key : δ ^ 2 * x ^ 3 * (0.1154 - 4 * η) ≤ c * δ * L ^ 2 * (x / 2) ^ 2 := by
    have : δ ^ 2 * x ^ 3 * (0.1154 - 4 * η) = δ ^ 2 * (0.1154 * x ^ 3) - 4 * η * δ ^ 2 * x ^ 3 := by
      ring
    rw [this]
    linarith
  have hpos : 0 < δ * x ^ 2 := by positivity
  have k2 : (δ * x ^ 2) * (δ * x * (0.1154 - 4 * η)) ≤ (δ * x ^ 2) * (c * L ^ 2 / 4) := by
    have e1 : (δ * x ^ 2) * (δ * x * (0.1154 - 4 * η)) = δ ^ 2 * x ^ 3 * (0.1154 - 4 * η) := by ring
    have e2 : (δ * x ^ 2) * (c * L ^ 2 / 4) = c * δ * L ^ 2 * (x / 2) ^ 2 := by ring
    rw [e1, e2]; exact key
  have k3 := le_of_mul_le_mul_left k2 hpos
  have hcL : 0 ≤ c * L ^ 2 := mul_nonneg hc (sq_nonneg L)
  have hm : 0 < 0.1154 - 4 * η := by linarith
  have k4 : 2.167 * c * L ^ 2 * (0.1154 - 4 * η) < δ * x * (0.1154 - 4 * η) :=
    mul_lt_mul_of_pos_right hbig hm
  nlinarith [mul_nonneg hcL hη0]

/-- CONDITIONAL ON `WeightedJθa (3/2) 1.0099 (10^13) (10^-13)`, the θ bound and the leaves:
for every `x ≥ 10^18` a Goldbach number lies in `(x, x + 2.19 log² x]`; `2.167 · 1.0099 = 2.1885`.
Real proof; `δ ≤ 10^-13` from U-1522's leaf `delta_small`. Unit U-1556. -/
theorem goldbach_219_of_weighted_a (hW : WeightedJθa (3 / 2) 1.0099 (10 ^ 13) (1 / 10 ^ 13))
    (hR6 : ∀ u : ℝ, 10 ^ 16 ≤ u → |θ u - u| ≤ u / 10 ^ 6) {x : ℝ} (hx : 10 ^ 18 ≤ x) :
    U1522.GoldbachIn x (x + 2.19 * Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  set δ := 2.19 * Real.log x ^ 2 / x with hδdef
  have hδ : 0 < δ := by positivity
  have hδ13 : δ ≤ 1 / 10 ^ 13 := by
    have h := U1522.delta_small hx
    have : δ ≤ 2.62 * Real.log x ^ 2 / x := by
      rw [hδdef]; apply div_le_div_of_nonneg_right _ hx0.le; nlinarith [sq_nonneg (Real.log x)]
    linarith
  have hδ1 : δ ≤ 1 := le_trans hδ13 (by norm_num)
  have hδx : δ * x = 2.19 * Real.log x ^ 2 := by rw [hδdef]; field_simp
  have hR : ∀ u : ℝ, x / 64 ≤ u → |θ u - u| ≤ 1 / 10 ^ 6 * u := by
    intro u hu
    have h := hR6 u (by linarith)
    calc |θ u - u| ≤ u / 10 ^ 6 := h
      _ = 1 / 10 ^ 6 * u := by ring
  have hup : 2.0001 / δ ≤ x := by
    rw [div_le_iff₀ hδ, mul_comm, hδx]; nlinarith
  have hlow : 1 ≤ 2.0001 / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have hL0 : 0 ≤ Real.log (2.0001 / δ) := Real.log_nonneg hlow
  have hLx : Real.log (2.0001 / δ) ≤ Real.log x := Real.log_le_log (by linarith) hup
  have hL2 : Real.log (2.0001 / δ) ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ hL0 hLx 2
  have hbig : 2.167 * 1.0099 * Real.log (2.0001 / δ) ^ 2 < δ * x := by
    rw [hδx]; nlinarith
  have h := goldbach_of_weighted_a hW (by norm_num) hR (by norm_num) le_rfl
    (by linarith) (by linarith) hδ hδ13 hδ1 hbig
  rwa [hδx] at h

/-- HEADLINE, CONDITIONAL ON ExplicitA, `HadamardKa (3/2)`, the diagonal bound 1.0068 (the
conclusion of `U6806.diag_u6806`), the θ bound `|θ u - u| ≤ u/10^6` for `u ≥ 10^16`, the
4·10^18 even check, and the open leaves of this file and U-1522 `goldbach_of_pair_ne`,
`delta_small`: for every `x ≥ 4` a sum of two odd primes lies in `(x, x + 2.19 log² x]`, against
2.62 with `W = W_2`. Real proof. Unit U-1556. -/
theorem goldbach_219_all {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ) (hH : HadamardKa (3 / 2) γ)
    (hD : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ∀ s : Finset ι,
      ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ 1.0068 * δ * Real.log (2.0001 / δ) ^ 2)
    (hT : ∀ u : ℝ, 10 ^ 16 ≤ u → |θ u - u| ≤ u / 10 ^ 6)
    (hEv : LeanLab.EvenGoldbachUpTo (4 * 10 ^ 18)) {x : ℝ} (hx : 4 ≤ x) :
    U1522.GoldbachIn x (x + 2.19 * Real.log x ^ 2) := by
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, ⟨p, q, hp, hq, hpo, hqo, hpq⟩, h1, h2⟩ := small_of hEv x (by linarith) hs
    have hlog : 1.386 ≤ Real.log x := by
      have h4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
      have h22 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      linarith
    refine ⟨p, q, hp, hq, hpo, hqo, ?_, ?_⟩
    · rw [hpq]; exact h1
    · rw [hpq]; nlinarith
  · exact goldbach_219_of_weighted_a (weightedJθa_of_explicit hE hH hD) hT (by linarith)

end LeanLab.Routes.U1556B
