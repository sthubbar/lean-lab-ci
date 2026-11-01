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
/-
CODEX task204, 2026-11-01. AI wrote the new Lean proofs.
Five of the six task leaves are proved. The quantitative dqt_Wa_le bound is open.
Its integrability component is proved by dqt_Wa_elementary.
The headline Goldbach conclusion remains CONDITIONAL. Binary Goldbach is open.
Build and axiom evidence is in Routes/build/codex-task204.log.
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

/-- The logarithmic substitution gives the exponential weight. Lab identity for U-1556. -/
theorem exp_Wa (a v : ℝ) :
    Real.exp v * Real.exp v * Wa a (Real.exp v) = Real.exp (-a * |v|) := by
  unfold Wa
  split_ifs with h
  · have hv : v ≤ 0 := Real.exp_le_one_iff.mp h
    rw [abs_of_pos (Real.exp_pos v), Real.rpow_def_of_pos (Real.exp_pos v),
      Real.log_exp, abs_of_nonpos hv, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · have hv : 0 < v := Real.one_lt_exp_iff.mp (lt_of_not_ge h)
    rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp, abs_of_pos hv,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

/-- A finite trigonometric sum has integrable square against any positive exponential decay. -/
theorem integrable_Fwa {a : ℝ} (ha : 0 < a) (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    Integrable (fun v => ‖F s c γ v‖ ^ 2 * Real.exp (-a * |v|)) := by
  have hi : IntegrableOn (fun v : ℝ => Real.exp (-a * |v|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic ha 0).congr_fun ?_ measurableSet_Iic
    intro v hv
    change v ≤ 0 at hv
    change Real.exp (a * v) = Real.exp (-a * |v|)
    rw [abs_of_nonpos hv]
    congr 1
    ring
  have hj : IntegrableOn (fun v : ℝ => Real.exp (-a * |v|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun ?_ measurableSet_Ioi
    intro v hv
    change 0 < v at hv
    change Real.exp (-a * v) = Real.exp (-a * |v|)
    rw [abs_of_pos hv]
  have hw : Integrable (fun v : ℝ => Real.exp (-a * |v|)) := by
    have h := hi.union hj
    rwa [Iic_union_Ioi, integrableOn_univ] at h
  set B := ∑ i ∈ s, ‖c i‖
  have hb : ∀ v, ‖F s c γ v‖ ≤ B := by
    intro v
    unfold LeanLab.ChirreHagen2025.SmoothKernel.F
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_exp]
    simp
  refine (hw.const_mul (B ^ 2)).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul ((continuous_F s c γ).norm.pow 2)
    fun_prop
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb v) 2)
      (Real.exp_pos _).le

/-- LEAF. Unit U-1556. SmoothY `integrableOn_P_W` for `w_a`: for `a > 0`, `x > 0` and a finite
sum `P(y) = Σ_i c_i y^{1/2 + iγ_i}`, `|P(y)|² W_a(y/x)` is integrable on `y > 0`.
Plain math: `|P(y)|² ≪ y`, and `y · y^{a-2}` near 0, `y · y^{-2-a}` near ∞ are integrable. -/
theorem integrableOn_P_Wa {a : ℝ} (ha : 0 < a) (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ}
    (hx : 0 < x) : IntegrableOn (fun y => ‖P s c γ y‖ ^ 2 * Wa a (y / x)) (Ioi 0) := by
  have hF := (integrable_Fwa ha s (cx c γ x) γ).const_mul x
  have e : (fun v => x * (‖F s (cx c γ x) γ v‖ ^ 2 * Real.exp (-a * |v|)))
      = fun v => Real.exp v • (‖P s c γ (x * Real.exp v)‖ ^ 2 * Wa a (x * Real.exp v / x)) := by
    funext v
    rw [smul_eq_mul, normSq_P_exp s c γ hx, mul_div_cancel_left₀ _ hx.ne', ← exp_Wa a v]
    ring
  rw [e, integrable_comp_exp (fun u => ‖P s c γ (x * u)‖ ^ 2 * Wa a (x * u / x))] at hF
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun y => ‖P s c γ y‖ ^ 2 * Wa a (y / x)) 0 hx).mp hF
  rwa [mul_zero] at h

/-- Rescaling the existing SmoothKernel bound gives the kernel at every positive decay rate. -/
theorem integral_Fwa_le {a : ℝ} (ha : 0 < a) (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    ∫ v, ‖F s c γ v‖ ^ 2 * Real.exp (-a * |v|)
      ≤ ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, Ka a (γ i - γ j) := by
  let r : ℝ := 2 / a
  have hr : 0 < r := by dsimp [r]; positivity
  have har : a * r = 2 := by dsimp [r]; field_simp
  have he : (fun v => ‖F s c γ (r * v)‖ ^ 2 * Real.exp (-a * |r * v|)) =
      fun v => ‖F s c (fun i => γ i * r) v‖ ^ 2 * w v := by
    funext v
    have hF : F s c γ (r * v) = F s c (fun i => γ i * r) v := by
      unfold LeanLab.ChirreHagen2025.SmoothKernel.F
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      push_cast
      ring
    rw [hF, abs_mul, abs_of_pos hr]
    congr 2
    calc -a * (r * |v|) = -(a * r) * |v| := by ring
      _ = -2 * |v| := by rw [har]
  have hchange := MeasureTheory.Measure.integral_comp_mul_left
    (fun v => ‖F s c γ v‖ ^ 2 * Real.exp (-a * |v|)) r
  rw [he, abs_of_pos (inv_pos.mpr hr), smul_eq_mul] at hchange
  have hbound := mul_le_mul_of_nonneg_left (integral_normSq_le s c (fun i => γ i * r)) hr.le
  have hK : ∀ u v : ℝ, r * K (u * r - v * r) = Ka a (u - v) := by
    intro u v
    dsimp [r, K, Ka]
    have ha0 : a ≠ 0 := ha.ne'
    have hden : a ^ 2 + (u - v) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    <;> ring
  have hsum : r * (∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, K (γ i * r - γ j * r)) =
      ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, Ka a (γ i - γ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, mul_comm r, mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact hK _ _
  rw [hsum] at hbound
  have hid : r * (∫ v, ‖F s c (fun i => γ i * r) v‖ ^ 2 * w v) =
      ∫ v, ‖F s c γ v‖ ^ 2 * Real.exp (-a * |v|) := by
    rw [hchange]
    field_simp
  rwa [hid] at hbound

/-- LEAF. Unit U-1556. SmoothY `integral_P_W_le` for `w_a`: for `a > 0`, `x > 0`,
`∫_0^∞ |P(y)|² W_a(y/x) dy ≤ x² Σ_i |c_i|² Σ_j 2a/(a² + (γ_i - γ_j)²)`.
Plain math: `y = x e^v` turns the left side into `x² ∫ |Σ_i c_i x^{iγ_i} e^{iγ_i v}|² e^{-a|v|} dv`;
expand, the Fourier transform of `e^{-a|v|}` is `K_a ≥ 0`, and `|b_i b_j| ≤ (|b_i|² + |b_j|²)/2`. -/
theorem integral_P_Wa_le {a : ℝ} (ha : 0 < a) (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) {x : ℝ}
    (hx : 0 < x) :
    ∫ y in Ioi 0, ‖P s c γ y‖ ^ 2 * Wa a (y / x)
      ≤ x ^ 2 * ∑ i ∈ s, ‖c i‖ ^ 2 * ∑ j ∈ s, Ka a (γ i - γ j) := by
  have h1 := integral_comp_mul_left_Ioi
    (fun y => ‖P s c γ y‖ ^ 2 * Wa a (y / x)) 0 hx
  rw [mul_zero] at h1
  have h2 := integral_comp_exp (fun u => ‖P s c γ (x * u)‖ ^ 2 * Wa a (x * u / x))
  rw [← h2, smul_eq_mul] at h1
  have e : (fun v => Real.exp v • (‖P s c γ (x * Real.exp v)‖ ^ 2 * Wa a (x * Real.exp v / x)))
      = fun v => x * (‖F s (cx c γ x) γ v‖ ^ 2 * Real.exp (-a * |v|)) := by
    funext v
    rw [smul_eq_mul, normSq_P_exp s c γ hx, mul_div_cancel_left₀ _ hx.ne', ← exp_Wa a v]
    ring
  rw [e, integral_const_mul] at h1
  have he : (∫ y in Ioi 0, ‖P s c γ y‖ ^ 2 * Wa a (y / x)) =
      x ^ 2 * ∫ v, ‖F s (cx c γ x) γ v‖ ^ 2 * Real.exp (-a * |v|) := by
    have h := congrArg (fun r : ℝ => x * r) h1
    field_simp at h
    simpa only [neg_mul] using h.symm
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
  simpa only [norm_cx c γ hx] using integral_Fwa_le ha s (cx c γ x) γ

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

/-- Exponential form of a power moment of Wa. -/
theorem exp_Wa_moment (a q v : ℝ) :
    Real.exp v * (Real.exp v) ^ q * Wa a (Real.exp v) =
      Real.exp ((q - 1) * v - a * |v|) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp]
  unfold Wa
  split_ifs with h
  · have hv : v ≤ 0 := Real.exp_le_one_iff.mp h
    rw [abs_of_pos (Real.exp_pos v), Real.rpow_def_of_pos (Real.exp_pos v),
      Real.log_exp, abs_of_nonpos hv, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · have hv : 0 < v := Real.one_lt_exp_iff.mp (lt_of_not_ge h)
    rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp, abs_of_pos hv,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

/-- The convergent power moments of Wa have an elementary exact value. -/
theorem Wa_moment {a q x : ℝ} (hx : 0 < x) (hl : 0 < q + a - 1) (hr : q - a - 1 < 0) :
    IntegrableOn (fun y : ℝ => y ^ q * Wa a (y / x)) (Ioi 0) ∧
      (∫ y in Ioi 0, y ^ q * Wa a (y / x)) =
        x * x ^ q * (1 / (q + a - 1) - 1 / (q - a - 1)) := by
  let g : ℝ → ℝ := fun v => Real.exp ((q - 1) * v - a * |v|)
  have heL : ∀ v ∈ Iic (0 : ℝ), g v = Real.exp ((q + a - 1) * v) := by
    intro v hv
    change v ≤ 0 at hv
    dsimp [g]
    rw [abs_of_nonpos hv]
    congr 1
    ring
  have heR : ∀ v ∈ Ioi (0 : ℝ), g v = Real.exp ((q - a - 1) * v) := by
    intro v hv
    change 0 < v at hv
    dsimp [g]
    rw [abs_of_pos hv]
    congr 1
    ring
  have hiL : IntegrableOn g (Iic 0) :=
    (integrableOn_exp_mul_Iic hl 0).congr_fun (fun v hv => (heL v hv).symm) measurableSet_Iic
  have hiR : IntegrableOn g (Ioi 0) :=
    (integrableOn_exp_mul_Ioi hr 0).congr_fun (fun v hv => (heR v hv).symm) measurableSet_Ioi
  have hi : Integrable g := by
    have h := hiL.union hiR
    rwa [Iic_union_Ioi, integrableOn_univ] at h
  have hIg : (∫ v, g v) = 1 / (q + a - 1) - 1 / (q - a - 1) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hiL hiR]
    rw [setIntegral_congr_fun measurableSet_Iic heL,
      setIntegral_congr_fun measurableSet_Ioi heR,
      integral_exp_mul_Iic hl, integral_exp_mul_Ioi hr]
    simp
    ring
  have he : (fun v => Real.exp v • ((x * Real.exp v) ^ q * Wa a (x * Real.exp v / x))) =
      fun v => x ^ q * g v := by
    funext v
    rw [smul_eq_mul, mul_div_cancel_left₀ _ hx.ne', Real.mul_rpow hx.le (Real.exp_pos v).le]
    calc Real.exp v * (x ^ q * (Real.exp v) ^ q * Wa a (Real.exp v)) =
        x ^ q * (Real.exp v * (Real.exp v) ^ q * Wa a (Real.exp v)) := by ring
      _ = _ := by rw [exp_Wa_moment]
  have hcomp : IntegrableOn (fun u => (x * u) ^ q * Wa a (x * u / x)) (Ioi 0) := by
    apply (integrable_comp_exp _).mp
    rw [he]
    exact hi.const_mul _
  have hI := (integrableOn_Ioi_comp_mul_left_iff
    (fun y : ℝ => y ^ q * Wa a (y / x)) 0 hx).mp hcomp
  rw [mul_zero] at hI
  refine ⟨hI, ?_⟩
  have hscale := integral_comp_mul_left_Ioi (fun y : ℝ => y ^ q * Wa a (y / x)) 0 hx
  rw [mul_zero, ← integral_comp_exp (fun u => (x * u) ^ q * Wa a (x * u / x)),
    he, integral_const_mul, hIg, smul_eq_mul] at hscale
  have h := congrArg (fun r : ℝ => x * r) hscale
  rw [← mul_assoc x x⁻¹, mul_inv_cancel₀ hx.ne', one_mul] at h
  simpa only [mul_assoc] using h.symm

/-- LEAF. Unit U-1556. For `0 < δ ≤ 1`, `X ≥ 2`: `B_δ(y)² W_{3/2}(y/X)` is integrable on `y > 2`
with integral at most `3δ²X`. Plain math: `B_δ² ≤ δ²` for `y ≥ 2` (lab `Bf_sq_le`), and
`∫_0^X (y/X)^{-1/2} dy + ∫_X^∞ (y/X)^{-7/2} dy = 2X + X/2.5`. -/
theorem bias_Wa_le {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX : 2 ≤ X) :
    IntegrableOn (fun y => Bf δ y ^ 2 * Wa (3 / 2) (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, Bf δ y ^ 2 * Wa (3 / 2) (y / X) ≤ 3 * δ ^ 2 * X := by
  have hX0 : 0 < X := by linarith
  obtain ⟨hW, hIW⟩ := Wa_moment (a := 3 / 2) (q := 0) hX0 (by norm_num) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at hW hIW
  have hIW' : (∫ y in Ioi 0, Wa (3 / 2) (y / X)) = 12 / 5 * X := by
    norm_num at hIW
    linarith only [hIW]
  have hW2 := hW.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2))
  have hM := hW2.const_mul (δ ^ 2)
  have hpt : ∀ᵐ y ∂volume.restrict (Ioi (2 : ℝ)),
      Bf δ y ^ 2 * Wa (3 / 2) (y / X) ≤ δ ^ 2 * Wa (3 / 2) (y / X) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_le_mul_of_nonneg_right (Bf_sq_le hδ hδ1 hy.le) (Wa_nonneg _ _)
  have hB : IntegrableOn (fun y => Bf δ y ^ 2 * Wa (3 / 2) (y / X)) (Ioi 2) := by
    apply hM.mono' (((measurable_Bf δ).pow_const 2).mul (measurable_Wa_div _ _)).aestronglyMeasurable
    filter_upwards [hpt] with y hy
    change ‖Bf δ y ^ 2 * Wa (3 / 2) (y / X)‖ ≤ δ ^ 2 * Wa (3 / 2) (y / X)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Wa_nonneg _ _))]
    exact hy
  refine ⟨hB, ?_⟩
  have hmono := integral_mono_ae hB hM hpt
  rw [integral_const_mul] at hmono
  have hsub : (∫ y in Ioi 2, Wa (3 / 2) (y / X)) ≤ ∫ y in Ioi 0, Wa (3 / 2) (y / X) :=
    setIntegral_mono_set hW (Filter.Eventually.of_forall (fun y => Wa_nonneg _ _))
      (Filter.Eventually.of_forall (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2)))
  rw [hIW'] at hsub
  have hfinal := mul_le_mul_of_nonneg_left hsub (sq_nonneg δ)
  nlinarith [mul_nonneg (sq_nonneg δ) hX0.le]

/-- The elementary Chebyshev bound proves integrability but has cubic centre dependence. -/
theorem dqt_Wa_elementary {δ X : ℝ} (hδ : 0 < δ) (hX : 0 < X) :
    IntegrableOn (fun y => Dqt δ y ^ 2 * Wa (3 / 2) (y / X)) (Ioi 2) ∧
      (∫ y in Ioi 2, Dqt δ y ^ 2 * Wa (3 / 2) (y / X)) ≤
        588 / 5 * (1 + δ) ^ 2 * X ^ 3 := by
  obtain ⟨hW, hIW⟩ := Wa_moment (a := 3 / 2) (q := 2) hX (by norm_num) (by norm_num)
  simp only [Real.rpow_two] at hW hIW
  have hIW' : (∫ y in Ioi 0, y ^ 2 * Wa (3 / 2) (y / X)) = 12 / 5 * X ^ 3 := by
    norm_num at hIW
    nlinarith only [hIW]
  have hW2 := hW.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2))
  have hM := hW2.const_mul (49 * (1 + δ) ^ 2)
  have hpt : ∀ᵐ y ∂volume.restrict (Ioi (2 : ℝ)),
      Dqt δ y ^ 2 * Wa (3 / 2) (y / X) ≤
        (49 * (1 + δ) ^ 2) * (y ^ 2 * Wa (3 / 2) (y / X)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 ≤ y := by linarith [show 2 < y from hy]
    have hD0 : 0 ≤ Dqt δ y := by
      simpa only [Dqt, Dpt, fpt] using Dpt_nonneg hδ.le hy0
    have hp := psi_le_const_mul_self (x := (1 + δ) * y) (by positivity)
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    have hp7 : ψ ((1 + δ) * y) ≤ 7 * ((1 + δ) * y) :=
      hp.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    have hd : Dqt δ y ≤ 7 * (1 + δ) * y := by
      unfold Dqt
      linarith [theta_nonneg ((1 + δ) * y), theta_le_psi y]
    have hs : Dqt δ y ^ 2 ≤ 49 * (1 + δ) ^ 2 * y ^ 2 := by
      have hh := mul_le_mul hd hd hD0 (by positivity)
      nlinarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hs (Wa_nonneg (3 / 2) (y / X))
    nlinarith only [hh]
  have hD : IntegrableOn (fun y => Dqt δ y ^ 2 * Wa (3 / 2) (y / X)) (Ioi 2) := by
    apply hM.mono' (((measurable_Dqt δ).pow_const 2).mul (measurable_Wa_div _ _)).aestronglyMeasurable
    filter_upwards [hpt] with y hy
    change ‖Dqt δ y ^ 2 * Wa (3 / 2) (y / X)‖ ≤ (49 * (1 + δ) ^ 2) * (y ^ 2 * Wa (3 / 2) (y / X))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Wa_nonneg _ _))]
    exact hy
  refine ⟨hD, ?_⟩
  have hmono := integral_mono_ae hD hM hpt
  rw [integral_const_mul] at hmono
  have hsub : (∫ y in Ioi 2, y ^ 2 * Wa (3 / 2) (y / X)) ≤
      ∫ y in Ioi 0, y ^ 2 * Wa (3 / 2) (y / X) :=
    setIntegral_mono_set hW
      (Filter.Eventually.of_forall (fun y => mul_nonneg (sq_nonneg _) (Wa_nonneg _ _)))
      (Filter.Eventually.of_forall (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2)))
  rw [hIW'] at hsub
  have hfinal := mul_le_mul_of_nonneg_left hsub (by positivity : 0 ≤ 49 * (1 + δ) ^ 2)
  nlinarith only [hmono, hfinal]

/-- The elementary cubic majorant exceeds the requested bound at its threshold. -/
theorem elementary_dqt_bound_exceeds_target_at_threshold :
    1 / (10 : ℝ) ^ 6 * (1 / 10 ^ 13) * Real.log (2.0001 / (1 / 10 ^ 13)) ^ 2 * (10 ^ 13) ^ 2 <
      588 / 5 * (1 + 1 / 10 ^ 13) ^ 2 * (10 ^ 13) ^ 3 := by
  have h0 : 0 ≤ Real.log (2.0001 / (1 / (10 : ℝ) ^ 13)) := Real.log_nonneg (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2.0001 / (1 / (10 : ℝ) ^ 13))
  have hs := pow_le_pow_left₀ h0 hlog 2
  norm_num at hs ⊢
  nlinarith only [hs]

/-- LEAF. Unit U-1556. Unconditional: for `0 < δ ≤ 10^-13`, `X ≥ 10^13`, with
`D = (ψ - θ)((1+δ)y) - (ψ - θ)(y)`, `D² W_{3/2}(y/X)` is integrable on `y > 2` and its integral
is at most `10^-6 δ log²(2.0001/δ) X²`. Plain math: as `U1556.dqt_W_le`; the heavier weight
`(X/y)^{1/2}` below `X` turns the prime square sum into `δ √X Σ_{p ≤ √X} p log² p ≪ δ X^{3/2} log X`. -/
theorem dqt_Wa_le {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X) :
    IntegrableOn (fun y => Dqt δ y ^ 2 * Wa (3 / 2) (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, Dqt δ y ^ 2 * Wa (3 / 2) (y / X)
        ≤ 1 / 10 ^ 6 * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  refine ⟨(dqt_Wa_elementary hδ (by linarith)).1, ?_⟩
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


/-- The pairing weight is symmetric about one half. -/
theorem Ua_symm (s : ℝ) : Ua (1 - s) = Ua s := by
  unfold Ua
  rw [sub_sub_cancel, mul_comm]

/-- On the positive left half the fourth power of the weight is rational. -/
theorem Ua_fourth_left {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) :
    Ua s ^ 4 = 1 / (256 * s * (1 - s) ^ 7) := by
  have ht : 0 < 1 - s := by linarith
  have hw1 : Wa (3 / 2) (2 * s) = (2 * s) ^ (-1 / 2 : ℝ) := by
    unfold Wa
    rw [if_pos (by linarith), abs_of_pos (by positivity)]
    norm_num
  have hw2 : Wa (3 / 2) (2 * (1 - s)) = (2 * (1 - s)) ^ (-7 / 2 : ℝ) := by
    unfold Wa
    split_ifs with h
    · have he : 2 * (1 - s) = 1 := by linarith
      simp [he]
    · norm_num
  have hp1 : (Wa (3 / 2) (2 * s)) ^ 2 = (2 * s)⁻¹ := by
    rw [hw1, ← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_neg_one]
  have hp2 : (Wa (3 / 2) (2 * (1 - s))) ^ 2 = ((2 * (1 - s)) ^ 7)⁻¹ := by
    rw [hw2, ← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_neg (by positivity : 0 ≤ 2 * (1 - s))]
  calc Ua s ^ 4 = (Ua s ^ 2) ^ 2 := by ring
    _ = _ := by
      rw [Ua_sq, mul_pow, hp1, hp2]
      field_simp
      <;> ring

/-- The truncated pairing weight is bounded by one. -/
theorem Ua_le_one_interval {s : ℝ} (hs : 1 / 64 ≤ s) (hs1 : s ≤ 63 / 64) : Ua s ≤ 1 := by
  have hleft : ∀ t : ℝ, 1 / 64 ≤ t → t ≤ 1 / 2 → Ua t ≤ 1 := by
    intro t ht ht1
    have ht0 : 0 < t := by linarith
    have htc : 0 < 1 - t := by linarith
    have hden : 1 ≤ 256 * t * (1 - t) ^ 7 := by
      by_cases ht8 : t ≤ 1 / 8
      · have hp : (7 / 8 : ℝ) ^ 7 ≤ (1 - t) ^ 7 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 7
        have hm := mul_le_mul ht hp (by norm_num : (0 : ℝ) ≤ (7 / 8 : ℝ) ^ 7) ht0.le
        norm_num at hm
        nlinarith only [hm]
      · let h := 1 - 2 * t
        have hh0 : 0 ≤ h := by dsimp [h]; linarith
        have hh1 : h ≤ 3 / 4 := by dsimp [h]; linarith
        have hb : 1 + 7 * h ≤ (1 + h) ^ 7 := by
          have hp : 0 ≤ 21 * h ^ 2 + 35 * h ^ 3 + 35 * h ^ 4 + 21 * h ^ 5 + 7 * h ^ 6 + h ^ 7 := by positivity
          nlinarith only [hp]
        have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1 - h by linarith)
        have hk := mul_nonneg hh0 (show 0 ≤ 6 - 7 * h by linarith)
        have he : 256 * t * (1 - t) ^ 7 = (1 - h) * (1 + h) ^ 7 := by dsimp [h]; ring
        rw [he]
        nlinarith only [hm, hk]
    apply (pow_le_one_iff_of_nonneg (Ua_nonneg _) (by decide : (4 : ℕ) ≠ 0)).mp
    rw [Ua_fourth_left ht0 ht1]
    exact (div_le_one (by positivity)).mpr hden
  by_cases hs2 : s ≤ 1 / 2
  · exact hleft s hs hs2
  · rw [← Ua_symm]
    exact hleft (1 - s) (by linarith) (by linarith)

/-- The scaled factor in the cross term is bounded on the truncated interval. -/
theorem Ua_phi_le {s : ℝ} (hs : 1 / 64 ≤ s) (hs1 : s ≤ 63 / 64) :
    Ua s * (1 - s) ≤ 3 / 4 := by
  have hs0 : 0 < s := by linarith
  have hsc : 0 < 1 - s := by linarith
  by_cases hs4 : 1 / 4 ≤ s
  · have hu := Ua_le_one_interval hs hs1
    nlinarith [mul_nonneg (show 0 ≤ 1 - s by linarith) (show 0 ≤ 1 - Ua s by linarith)]
  · have hs2 : s ≤ 1 / 2 := by linarith
    have hp : (Ua s * (1 - s)) ^ 4 = 1 / (256 * s * (1 - s) ^ 3) := by
      rw [mul_pow, Ua_fourth_left hs0 hs2]
      field_simp
      <;> ring
    have hden : (4 / 3 : ℝ) ^ 4 ≤ 256 * s * (1 - s) ^ 3 := by
      by_cases hs16 : s ≤ 1 / 16
      · have hc : (15 / 16 : ℝ) ^ 3 ≤ (1 - s) ^ 3 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 3
        have hm := mul_le_mul hs hc (by norm_num : (0 : ℝ) ≤ (15 / 16 : ℝ) ^ 3) hs0.le
        norm_num at hm
        nlinarith only [hm]
      · have hc : (3 / 4 : ℝ) ^ 3 ≤ (1 - s) ^ 3 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 3
        have hm := mul_le_mul (show 1 / 16 ≤ s by linarith) hc (by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ 3) hs0.le
        norm_num at hm
        nlinarith only [hm]
    apply (pow_le_pow_iff_left₀ (mul_nonneg (Ua_nonneg _) hsc.le) (by norm_num : (0 : ℝ) ≤ 3 / 4) (by decide : (4 : ℕ) ≠ 0)).mp
    rw [hp, div_le_iff₀ (by positivity)]
    norm_num at hden ⊢
    nlinarith only [hden]


set_option maxHeartbeats 2000000 in
/-- The positive left branch of the cross factor. -/
theorem Ua_phi_left {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) :
    Ua s * (1 - s) = s ^ (-1 / 4 : ℝ) * (1 - s) ^ (-3 / 4 : ℝ) / 4 := by
  have ht : 0 < 1 - s := by linarith
  apply (pow_left_inj₀ (mul_nonneg (Ua_nonneg _) ht.le) (by positivity) (by decide : (4 : ℕ) ≠ 0)).mp
  rw [mul_pow, Ua_fourth_left hs hs1, div_pow, mul_pow,
    ← Real.rpow_mul_natCast hs.le, ← Real.rpow_mul_natCast ht.le]
  norm_num [Real.rpow_neg_one, Real.rpow_neg ht.le]
  field_simp
  <;> ring

set_option maxHeartbeats 2000000 in
/-- The positive right branch of the cross factor. -/
theorem Ua_phi_right {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s < 1) :
    Ua s * (1 - s) = (1 - s) ^ (3 / 4 : ℝ) * s ^ (-7 / 4 : ℝ) / 4 := by
  have hs0 : 0 < s := by linarith
  have ht : 0 < 1 - s := by linarith
  apply (pow_left_inj₀ (mul_nonneg (Ua_nonneg _) ht.le) (by positivity) (by decide : (4 : ℕ) ≠ 0)).mp
  rw [mul_pow, ← Ua_symm s, Ua_fourth_left ht (by linarith), sub_sub_cancel,
    div_pow, mul_pow, ← Real.rpow_mul_natCast ht.le, ← Real.rpow_mul_natCast hs0.le]
  norm_num [Real.rpow_neg hs0.le]
  field_simp
  <;> ring

set_option maxHeartbeats 2000000 in
/-- The derivative of the explicitly scaled left branch is three quarters times Ua. -/
theorem scaled_phi_left_deriv {s p : ℝ} (hs : 0 < s) (hp : 0 < p) (hps : p * s ≤ 1 / 2) :
    HasDerivAt (fun q : ℝ => q * ((q * s) ^ (-1 / 4 : ℝ) * (1 - q * s) ^ (-3 / 4 : ℝ) / 4))
      (3 / 4 * Ua (p * s)) p := by
  have hps0 : 0 < p * s := mul_pos hp hs
  have ht : 0 < 1 - p * s := by linarith
  have h₁ := ((hasDerivAt_id p).mul_const s).rpow_const
    (p := (-1 / 4 : ℝ)) (Or.inl hps0.ne')
  have h₂ := ((hasDerivAt_const p (1 : ℝ)).sub ((hasDerivAt_id p).mul_const s)).rpow_const
    (p := (-3 / 4 : ℝ)) (Or.inl ht.ne')
  have hU : Ua (p * s) = ((p * s) ^ (-1 / 4 : ℝ) * (1 - p * s) ^ (-3 / 4 : ℝ) / 4) / (1 - p * s) :=
    (eq_div_iff ht.ne').mpr (Ua_phi_left hps0 hps)
  convert (hasDerivAt_id p).mul ((h₁.mul h₂).div_const 4) using 1 <;> try { funext q; rfl }
  dsimp
  rw [Real.rpow_sub_one hps0.ne' (-1 / 4), Real.rpow_sub_one ht.ne' (-3 / 4), hU]
  field_simp
  <;> ring

set_option maxHeartbeats 2000000 in
/-- The derivative of the explicitly scaled right branch is minus three quarters times Ua. -/
theorem scaled_phi_right_deriv {s p : ℝ} (hs : 0 < s) (hp : 0 < p)
    (hps : 1 / 2 ≤ p * s) (hps1 : p * s < 1) :
    HasDerivAt (fun q : ℝ => q * ((1 - q * s) ^ (3 / 4 : ℝ) * (q * s) ^ (-7 / 4 : ℝ) / 4))
      (-3 / 4 * Ua (p * s)) p := by
  have hps0 : 0 < p * s := mul_pos hp hs
  have ht : 0 < 1 - p * s := by linarith
  have h₁ := ((hasDerivAt_const p (1 : ℝ)).sub ((hasDerivAt_id p).mul_const s)).rpow_const
    (p := (3 / 4 : ℝ)) (Or.inl ht.ne')
  have h₂ := ((hasDerivAt_id p).mul_const s).rpow_const
    (p := (-7 / 4 : ℝ)) (Or.inl hps0.ne')
  have hU : Ua (p * s) = ((1 - p * s) ^ (3 / 4 : ℝ) * (p * s) ^ (-7 / 4 : ℝ) / 4) / (1 - p * s) :=
    (eq_div_iff ht.ne').mpr (Ua_phi_right hps hps1)
  convert (hasDerivAt_id p).mul ((h₁.mul h₂).div_const 4) using 1 <;> try { funext q; rfl }
  dsimp
  rw [Real.rpow_sub_one ht.ne' (3 / 4), Real.rpow_sub_one hps0.ne' (-7 / 4), hU]
  field_simp
  <;> ring

set_option maxHeartbeats 2000000 in
/-- The explicitly scaled left cross factor is three quarters Lipschitz. -/
theorem phi_scaled_left_a {p q s : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hs : 0 < s)
    (hps : 1 / 64 ≤ p * s) (hqs : q * s ≤ 1 / 2) :
    |q * (Ua (q * s) * (1 - q * s)) - p * (Ua (p * s) * (1 - p * s))| ≤ 3 / 4 * (q - p) := by
  let H : ℝ → ℝ := fun q => q * ((q * s) ^ (-1 / 4 : ℝ) * (1 - q * s) ^ (-3 / 4 : ℝ) / 4)
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hbound : ∀ z ∈ Icc p q, ‖3 / 4 * Ua (z * s)‖ ≤ 3 / 4 := by
    intro z hz
    have hlo : 1 / 64 ≤ z * s := hps.trans (mul_le_mul_of_nonneg_right hz.1 hs.le)
    have hhi : z * s ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hz.2 hs.le).trans hqs
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (Ua_nonneg _))]
    nlinarith [Ua_le_one_interval hlo (by linarith)]
  have hd : ∀ z ∈ Icc p q, HasDerivWithinAt H (3 / 4 * Ua (z * s)) (Icc p q) z := by
    intro z hz
    exact (scaled_phi_left_deriv hs (lt_of_lt_of_le hp hz.1)
      ((mul_le_mul_of_nonneg_right hz.2 hs.le).trans hqs)).hasDerivWithinAt
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Icc p q)
    (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq)
  dsimp [H] at h
  rw [← Ua_phi_left (mul_pos hq hs) hqs,
    ← Ua_phi_left (mul_pos hp hs) ((mul_le_mul_of_nonneg_right hpq hs.le).trans hqs)] at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpq)] using h

set_option maxHeartbeats 2000000 in
/-- The explicitly scaled right cross factor is three quarters Lipschitz. -/
theorem phi_scaled_right_a {p q s : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hs : 0 < s)
    (hps : 1 / 2 ≤ p * s) (hqs : q * s ≤ 63 / 64) :
    |q * (Ua (q * s) * (1 - q * s)) - p * (Ua (p * s) * (1 - p * s))| ≤ 3 / 4 * (q - p) := by
  let H : ℝ → ℝ := fun q => q * ((1 - q * s) ^ (3 / 4 : ℝ) * (q * s) ^ (-7 / 4 : ℝ) / 4)
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hbound : ∀ z ∈ Icc p q, ‖-3 / 4 * Ua (z * s)‖ ≤ 3 / 4 := by
    intro z hz
    have hlo : 1 / 2 ≤ z * s := hps.trans (mul_le_mul_of_nonneg_right hz.1 hs.le)
    have hhi : z * s ≤ 63 / 64 := (mul_le_mul_of_nonneg_right hz.2 hs.le).trans hqs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Ua_nonneg _)]
    norm_num
    nlinarith [Ua_le_one_interval (by linarith) hhi]
  have hd : ∀ z ∈ Icc p q, HasDerivWithinAt H (-3 / 4 * Ua (z * s)) (Icc p q) z := by
    intro z hz
    exact (scaled_phi_right_deriv hs (lt_of_lt_of_le hp hz.1)
      (hps.trans (mul_le_mul_of_nonneg_right hz.1 hs.le))
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hz.2 hs.le) (by linarith))).hasDerivWithinAt
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Icc p q)
    (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq)
  dsimp [H] at h
  rw [← Ua_phi_right (hps.trans (mul_le_mul_of_nonneg_right hpq hs.le)) (by linarith),
    ← Ua_phi_right hps (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hpq hs.le) (by linarith))] at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpq)] using h

set_option maxHeartbeats 2000000 in
/-- Multiplicative dilation of the truncated cross factor. -/
theorem phi_dilate_a {q s : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hqs : 1 / 64 ≤ q * s) (hs1 : s ≤ 63 / 64) :
    |q * (Ua (q * s) * (1 - q * s)) - Ua s * (1 - s)| ≤ 3 / 4 * (1 - q) := by
  have hs : 0 < s := by
    have hp : 0 < q * s := by linarith
    by_contra hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_gt hn)
    linarith
  have hqs1 : q * s ≤ s := by nlinarith
  by_cases hleft : s ≤ 1 / 2
  · have h := phi_scaled_left_a hq hq1 hs hqs (by simpa using hleft)
    simpa only [one_mul, abs_sub_comm] using h
  · by_cases hright : 1 / 2 ≤ q * s
    · have h := phi_scaled_right_a hq hq1 hs hright (by simpa using hs1)
      simpa only [one_mul, abs_sub_comm] using h
    · let r := 1 / (2 * s)
      have hr : 0 < r := by dsimp [r]; positivity
      have hrs : r * s = 1 / 2 := by dsimp [r]; field_simp
      have hqr : q ≤ r := by
        dsimp [r]
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hr1 : r ≤ 1 := by
        dsimp [r]
        rw [div_le_one (by positivity)]
        linarith
      have hL := phi_scaled_left_a hq hqr hs hqs (le_of_eq hrs)
      have hR := phi_scaled_right_a hr hr1 hs (le_of_eq hrs.symm) (by simpa using hs1)
      simp only [one_mul] at hR
      have htri := abs_sub_le (q * (Ua (q * s) * (1 - q * s)))
        (r * (Ua (r * s) * (1 - r * s))) (Ua s * (1 - s))
      rw [abs_sub_comm (q * _) (r * _)] at htri
      rw [abs_sub_comm (r * _) (Ua s * (1 - s))] at htri
      linarith


set_option maxHeartbeats 2000000 in
/-- LEAF. Unit U-1556. As U-1522 `cross_le` with `U_a`: with `|θ(u) - u| ≤ ηu` for `u ≥ x/64`,
`|cross| ≤ 4ηδ²x³`. -/
theorem cross_le_a {x δ η : ℝ} (hx : 128 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η)
    (hR : ∀ u : ℝ, x / 64 ≤ u → |θ u - u| ≤ η * u) :
    |crossTa x δ| ≤ 4 * η * δ ^ 2 * x ^ 3 := by
  have hxpos : 0 < x := by linarith
  have hxne : x ≠ 0 := hxpos.ne'
  let a := x / 64
  let b := 63 * x / 64
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hba : b - a ≤ x := by dsimp [a, b]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hbx : b ≤ x := by dsimp [b]; linarith
  have hE : ∀ y, a ≤ y → |U1522.Eθ δ y| ≤ η * (2 + δ) * y := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans ha.le hy
    have hky : a ≤ (1 + δ) * y := by nlinarith
    have h1 := hR ((1 + δ) * y) hky
    have h2 := hR y hy
    have he : U1522.Eθ δ y = (θ ((1 + δ) * y) - (1 + δ) * y) - (θ y - y) := by
      unfold U1522.Eθ
      ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  by_cases hdlarge : 1 / 3 ≤ δ
  · have hbnd : |∫ t in a..b, Ua (t / x) *
        (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t)| ≤
        (η * (2 + δ) * x ^ 2 / 2) * (b - a) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a) (b := b) (C := η * (2 + δ) * x ^ 2 / 2)
        (f := fun t => Ua (t / x) * (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t))
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
      apply h
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hxt0 : 0 ≤ x - t := by linarith [ht.2]
      have hxt : a ≤ x - t := by dsimp [a, b] at *; linarith [ht.2]
      have he1 := hE t ht.1.le
      have he2 := hE (x - t) hxt
      have hu0 : 0 ≤ Ua (t / x) := Real.sqrt_nonneg _
      have hu1 : Ua (t / x) ≤ 1 := Ua_le_one_interval
        ((div_le_div_iff₀ (by norm_num) hxpos).mpr (by dsimp [a] at ht; linarith [ht.1]))
        ((div_le_div_iff₀ hxpos (by norm_num)).mpr (by dsimp [b] at ht; linarith [ht.2]))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0]
      calc
        _ ≤ Ua (t / x) * (|t * U1522.Eθ δ (x - t)| + |(x - t) * U1522.Eθ δ t|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hu0
        _ ≤ Ua (t / x) * (2 * η * (2 + δ) * (t * (x - t))) := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hxt0]
          nlinarith [mul_le_mul_of_nonneg_left he2 ht0, mul_le_mul_of_nonneg_left he1 hxt0]
        _ ≤ 2 * η * (2 + δ) * (t * (x - t)) := by
          exact mul_le_of_le_one_left (by positivity) hu1
        _ ≤ η * (2 + δ) * x ^ 2 / 2 := by
          nlinarith [mul_nonneg (show 0 ≤ η * (2 + δ) by positivity) (sq_nonneg (t - x / 2))]
    change |δ * (∫ t in a..b, Ua (t / x) *
      (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t))| ≤ _
    rw [abs_mul, abs_of_pos hδ]
    calc
      _ ≤ δ * ((η * (2 + δ) * x ^ 2 / 2) * (b - a)) := mul_le_mul_of_nonneg_left hbnd hδ.le
      _ ≤ δ * ((η * (2 + δ) * x ^ 2 / 2) * x) := by gcongr
      _ ≤ 4 * η * δ ^ 2 * x ^ 3 := by
        have hh : 2 + δ ≤ 8 * δ := by linarith
        have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ η * δ * x ^ 3 / 2 by positivity)
        nlinarith
  · have hdsmall : δ ≤ 1 / 3 := le_of_lt (lt_of_not_ge hdlarge)
    let clamp : ℝ → ℝ := fun t => max a (min t b)
    let g : ℝ → ℝ := fun t => Ua (clamp t / x) * (x - clamp t)
    have hc : Continuous clamp := by dsimp [clamp]; fun_prop
    have hclamp : ∀ t, a ≤ clamp t ∧ clamp t ≤ b := by
      intro t
      dsimp [clamp]
      exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
    have hmap : ∀ t, clamp t / x ∈ Icc (1 / 64 : ℝ) (63 / 64) := by
      intro t
      have hlo : x / 64 ≤ clamp t := (hclamp t).1
      have hhi : clamp t ≤ 63 * x / 64 := (hclamp t).2
      constructor
      · exact (div_le_div_iff₀ (by norm_num) hxpos).mpr (by linarith only [hlo])
      · exact (div_le_div_iff₀ hxpos (by norm_num)).mpr (by linarith only [hhi])
    have hcU : Continuous (fun t => Ua (clamp t / x)) := by
      apply continuousOn_univ.mp
      exact continuous_Ua_interval.comp ((hc.div_const x).continuousOn) (fun t ht => hmap t)
    have hg : Continuous g := hcU.mul (continuous_const.sub hc)
    have hgform : ∀ t, a ≤ t → t ≤ b → g t = Ua (t / x) * (x - t) := by
      intro t ht ht1
      dsimp [g, clamp]
      rw [min_eq_left ht1, max_eq_right ht]
    have hgb : ∀ t, |g t| ≤ 3 / 4 * x := by
      intro t
      have hp := Ua_phi_le (hmap t).1 (hmap t).2
      have hc0 : 0 ≤ clamp t := le_trans ha.le (hclamp t).1
      have hcx : clamp t ≤ x := le_trans (hclamp t).2 hbx
      have he : g t = x * (Ua (clamp t / x) * (1 - clamp t / x)) := by
        dsimp [g]
        field_simp
        <;> ring
      rw [he, abs_mul, abs_of_pos hxpos, abs_of_nonneg
        (mul_nonneg (Ua_nonneg _) (by rw [sub_nonneg, div_le_one hxpos]; exact hcx))]
      nlinarith [mul_le_mul_of_nonneg_left hp hxpos.le]
    let q : ℝ := 1 / (1 + δ)
    have hk : 0 < 1 + δ := by linarith
    have hq : 0 < q := by dsimp [q]; positivity
    have hq1 : q ≤ 1 := by dsimp [q]; rw [div_le_one hk]; linarith
    have hqrel : q * (1 + δ) = 1 := by dsimp [q]; field_simp
    have hqd : 1 - q ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hq1)]
    have hD : ∀ u, (1 + δ) * a ≤ u → u ≤ b →
        |g (u / (1 + δ)) / (1 + δ) - g u| ≤ 3 / 4 * δ * x := by
      intro u hu0 hu1
      have hua : a ≤ u := by nlinarith
      have huqa : a ≤ u / (1 + δ) := by rw [le_div_iff₀ hk]; nlinarith
      have huqb : u / (1 + δ) ≤ b := by rw [div_le_iff₀ hk]; nlinarith
      have hearg : u / (1 + δ) / x = q * (u / x) := by dsimp [q]; ring
      have hlo : 1 / 64 ≤ q * (u / x) := by
        rw [← hearg]
        exact (div_le_div_iff₀ (by norm_num) hxpos).mpr (by dsimp [a] at huqa; linarith)
      have hhi : u / x ≤ 63 / 64 :=
        (div_le_div_iff₀ hxpos (by norm_num)).mpr (by dsimp [b] at hu1; linarith)
      have hd := phi_dilate_a hq hq1 hlo hhi
      have he : g (u / (1 + δ)) / (1 + δ) - g u =
          x * (q * (Ua (q * (u / x)) * (1 - q * (u / x))) - Ua (u / x) * (1 - u / x)) := by
        rw [hgform _ huqa huqb, hgform _ hua hu1]
        dsimp [q]
        field_simp
        <;> ring
      rw [he, abs_mul, abs_of_pos hxpos]
      calc _ ≤ x * (3 / 4 * (1 - q)) := mul_le_mul_of_nonneg_left hd hxpos.le
        _ ≤ 3 / 4 * δ * x := by nlinarith
    have iE : ∀ c d, IntervalIntegrable (U1522.Eθ δ) volume c d :=
      fun c d => LeanLab.ChirreHagen2025.Eθ_ii hδ c d
    have iEr : IntervalIntegrable (fun t => U1522.Eθ δ (x - t)) volume a b := by
      simpa only [sub_sub_cancel] using (iE (x - a) (x - b)).comp_sub_left x
    have hU : ContinuousOn (fun t => Ua (t / x)) (uIcc a b) := by
      apply continuous_Ua_interval.comp (continuous_id.div_const x).continuousOn
      intro t ht
      rw [uIcc_of_le hab] at ht
      change t / x ∈ Icc (1 / 64 : ℝ) (63 / 64)
      have hlo : x / 64 ≤ t := ht.1
      have hhi : t ≤ 63 * x / 64 := ht.2
      constructor
      · exact (div_le_div_iff₀ (by norm_num) hxpos).mpr (by linarith only [hlo])
      · exact (div_le_div_iff₀ hxpos (by norm_num)).mpr (by linarith only [hhi])
    have i1 : IntervalIntegrable (fun t => Ua (t / x) * t * U1522.Eθ δ (x - t)) volume a b :=
      iEr.continuousOn_mul (hU.mul continuous_id.continuousOn)
    have i2 := (iE a b).continuousOn_mul hg.continuousOn
    have href : (∫ t in a..b, Ua (t / x) * t * U1522.Eθ δ (x - t)) =
        ∫ t in a..b, g t * U1522.Eθ δ t := by
      calc
        _ = ∫ t in a..b, g (x - t) * U1522.Eθ δ (x - t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hab] at ht
          have hxt : a ≤ x - t ∧ x - t ≤ b := by dsimp [a, b] at *; constructor <;> linarith [ht.1, ht.2]
          change Ua (t / x) * t * U1522.Eθ δ (x - t) = g (x - t) * U1522.Eθ δ (x - t)
          rw [hgform _ hxt.1 hxt.2]
          have hearg : (x - t) / x = 1 - t / x := by field_simp <;> ring
          rw [hearg, Ua_symm, sub_sub_cancel]
        _ = _ := by
          rw [intervalIntegral.integral_comp_sub_left (fun u => g u * U1522.Eθ δ u) x]
          have he1 : x - b = a := by dsimp [a, b]; ring
          have he2 : x - a = b := by dsimp [a, b]; ring
          rw [he1, he2]
    have hcross : crossTa x δ = 2 * δ * ∫ t in a..b, g t * U1522.Eθ δ t := by
      unfold crossTa
      change δ * (∫ t in a..b, Ua (t / x) *
        (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t)) = _
      have he : (∫ t in a..b, Ua (t / x) * (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t)) =
          (∫ t in a..b, Ua (t / x) * t * U1522.Eθ δ (x - t)) + ∫ t in a..b, g t * U1522.Eθ δ t := by
        rw [← intervalIntegral.integral_add i1 i2]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        change Ua (t / x) * (t * U1522.Eθ δ (x - t) + (x - t) * U1522.Eθ δ t) =
          Ua (t / x) * t * U1522.Eθ δ (x - t) + g t * U1522.Eθ δ t
        rw [hgform _ ht.1 ht.2]
        ring
      rw [he, href]
      ring
    let ρ := (4 / 3 : ℝ) * b * η
    have hρ : ∀ u, a ≤ u → u ≤ (1 + δ) * b → |LeanLab.ChirreHagen2025.Rθ u| ≤ ρ := by
      intro u hu0 hu1
      have hr := hR u hu0
      change |θ u - u| ≤ ρ
      dsimp [ρ]
      nlinarith [mul_le_mul_of_nonneg_right hu1 hη,
        mul_nonneg (show 0 ≤ 1 / 3 - δ by linarith) (mul_nonneg hb.le hη)]
    have hcbd := LeanLab.ChirreHagen2025.cross_bound hg hδ ha
      (by dsimp [a, b]; nlinarith [mul_le_mul_of_nonneg_right hδ1 hxpos.le]) hρ hD
      (fun u hu0 hu1 => hgb u) (fun u hu0 hu1 => by
        rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
        have hh := hgb (u / (1 + δ))
        nlinarith [mul_nonneg hδ.le hxpos.le])
    change |∫ t in a..b, g t * U1522.Eθ δ t| ≤ _ at hcbd
    rw [hcross, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * δ)]
    calc
      _ ≤ (2 * δ) * ((3 / 4 * δ * x) * ρ * (b - a) + (3 / 4 * x) * ρ * (δ * b) + (3 / 4 * x) * ρ * (δ * a)) :=
        mul_le_mul_of_nonneg_left hcbd (by positivity)
      _ ≤ 4 * η * δ ^ 2 * x ^ 3 := by
        dsimp [a, b, ρ]
        have hp : 0 ≤ η * δ ^ 2 * x ^ 3 := by positivity
        nlinarith only [hp]


/-- A quartic change of variable removes the fractional powers from the left half main term. -/
theorem Ua_quartic_substitution {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    Ua (z ^ 4 / (1 + z ^ 4)) *
      ((z ^ 4 / (1 + z ^ 4)) * (1 - z ^ 4 / (1 + z ^ 4))) = z ^ 3 / 4 := by
  let s := z ^ 4 / (1 + z ^ 4)
  have hd : 0 < 1 + z ^ 4 := by positivity
  have hz4 : z ^ 4 ≤ 1 := pow_le_one₀ hz.le hz1
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 / 2 := by dsimp [s]; rw [div_le_iff₀ hd]; linarith
  have ht : 0 < 1 - s := by linarith
  have hw1 : Wa (3 / 2) (2 * s) = (2 * s) ^ (-1 / 2 : ℝ) := by
    unfold Wa
    rw [if_pos (by linarith), abs_of_pos (by positivity)]
    norm_num
  have hw2 : Wa (3 / 2) (2 * (1 - s)) = (2 * (1 - s)) ^ (-7 / 2 : ℝ) := by
    unfold Wa
    split_ifs with h
    · have he : 2 * (1 - s) = 1 := by linarith
      simp [he]
    · norm_num
  have hp1 : (Wa (3 / 2) (2 * s)) ^ 2 = (2 * s)⁻¹ := by
    rw [hw1, ← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_neg_one]
  have hp2 : (Wa (3 / 2) (2 * (1 - s))) ^ 2 = ((2 * (1 - s)) ^ 7)⁻¹ := by
    rw [hw2, ← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_neg (by positivity : 0 ≤ 2 * (1 - s))]
  have hu4 : Ua s ^ 4 = (2 * s)⁻¹ * ((2 * (1 - s)) ^ 7)⁻¹ := by
    calc Ua s ^ 4 = (Ua s ^ 2) ^ 2 := by ring
      _ = _ := by rw [Ua_sq, mul_pow, hp1, hp2]
  have hu : Ua s = (1 + z ^ 4) ^ 2 / (4 * z) := by
    apply (pow_left_inj₀ (Ua_nonneg _) (by positivity) (by decide : (4 : ℕ) ≠ 0)).mp
    rw [hu4]
    dsimp [s]
    field_simp
    <;> ring
  change Ua s * (s * (1 - s)) = _
  rw [hu]
  dsimp [s]
  field_simp
  <;> ring


set_option maxHeartbeats 2000000 in
/-- A twelve term geometric lower polynomial certifies the rational main integral. -/
theorem rational_main_integral_lower : (0.1154 : ℝ) ≤ ∫ z in (71 / 200 : ℝ)..1, 2 * z ^ 6 / (1 + z ^ 4) ^ 2 := by
  let Q : ℝ → ℝ := fun z => (4089 / 2048 : ℝ) * z ^ 6 + (-2025 / 512 : ℝ) * z ^ 10 + (11721 / 2048 : ℝ) * z ^ 14 + (-7099 / 1024 : ℝ) * z ^ 18 + (7265 / 1024 : ℝ) * z ^ 22 + (-6 / 1 : ℝ) * z ^ 26 + (4165 / 1024 : ℝ) * z ^ 30 + (-1093 / 512 : ℝ) * z ^ 34 + (1701 / 2048 : ℝ) * z ^ 38 + (-115 / 512 : ℝ) * z ^ 42 + (77 / 2048 : ℝ) * z ^ 46 + (-3 / 1024 : ℝ) * z ^ 50
  let G : ℝ → ℝ := fun z => (4089 / 14336 : ℝ) * z ^ 7 + (-2025 / 5632 : ℝ) * z ^ 11 + (3907 / 10240 : ℝ) * z ^ 15 + (-7099 / 19456 : ℝ) * z ^ 19 + (7265 / 23552 : ℝ) * z ^ 23 + (-2 / 9 : ℝ) * z ^ 27 + (4165 / 31744 : ℝ) * z ^ 31 + (-1093 / 17920 : ℝ) * z ^ 35 + (567 / 26624 : ℝ) * z ^ 39 + (-115 / 22016 : ℝ) * z ^ 43 + (77 / 96256 : ℝ) * z ^ 47 + (-1 / 17408 : ℝ) * z ^ 51
  have hd : ∀ z, HasDerivAt G (Q z) z := by
    intro z
    convert (((((((((((((hasDerivAt_pow 7 z).const_mul (4089 / 14336 : ℝ)).add ((hasDerivAt_pow 11 z).const_mul (-2025 / 5632 : ℝ))).add ((hasDerivAt_pow 15 z).const_mul (3907 / 10240 : ℝ))).add ((hasDerivAt_pow 19 z).const_mul (-7099 / 19456 : ℝ))).add ((hasDerivAt_pow 23 z).const_mul (7265 / 23552 : ℝ))).add ((hasDerivAt_pow 27 z).const_mul (-2 / 9 : ℝ))).add ((hasDerivAt_pow 31 z).const_mul (4165 / 31744 : ℝ))).add ((hasDerivAt_pow 35 z).const_mul (-1093 / 17920 : ℝ))).add ((hasDerivAt_pow 39 z).const_mul (567 / 26624 : ℝ))).add ((hasDerivAt_pow 43 z).const_mul (-115 / 22016 : ℝ))).add ((hasDerivAt_pow 47 z).const_mul (77 / 96256 : ℝ))).add ((hasDerivAt_pow 51 z).const_mul (-1 / 17408 : ℝ))) using 1 <;> dsimp [G, Q] <;> ring
  have hq : Continuous Q := by dsimp [Q]; fun_prop
  have hG : (∫ z in (71 / 200 : ℝ)..1, Q z) = G 1 - G (71 / 200) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z hz => hd z) (hq.intervalIntegrable _ _)
  have hnum : (0.1154 : ℝ) ≤ G 1 - G (71 / 200) := by norm_num [G]
  rw [← hG] at hnum
  refine hnum.trans ?_
  apply intervalIntegral.integral_mono_on (by norm_num) (hq.intervalIntegrable _ _) ?_
  · intro z hz
    have hz0 : 0 ≤ z := by linarith [hz.1]
    have hz4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz.2
    have hlast : 0 ≤ 13 - 12 * ((1 - z ^ 4) / 2) := by nlinarith [show 0 ≤ z ^ 4 by positivity]
    have hrem : 0 ≤ 2 * z ^ 6 * ((1 - z ^ 4) / 2) ^ 12 * (13 - 12 * ((1 - z ^ 4) / 2)) := mul_nonneg (by positivity) hlast
    have he : 2 * z ^ 6 - Q z * (1 + z ^ 4) ^ 2 =
        2 * z ^ 6 * ((1 - z ^ 4) / 2) ^ 12 * (13 - 12 * ((1 - z ^ 4) / 2)) := by dsimp [Q]; ring
    rw [le_div_iff₀ (by positivity : 0 < (1 + z ^ 4) ^ 2)]
    linarith
  · apply Continuous.intervalIntegrable
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z; positivity

/-- Exact rational lower integration gives the normalized main term. -/
theorem normalized_main_ge_a :
    (0.1154 : ℝ) ≤ ∫ s in (1 / 64 : ℝ)..(63 / 64), Ua s * (s * (1 - s)) := by
  let f : ℝ → ℝ := fun s => Ua s * (s * (1 - s))
  have hf : ContinuousOn f (Icc (1 / 64 : ℝ) (63 / 64)) := by
    apply continuous_Ua_interval.mul
    apply Continuous.continuousOn
    fun_prop
  have hfi : IntervalIntegrable f volume (1 / 64) (63 / 64) := hf.intervalIntegrable_of_Icc (by norm_num : (1 / 64 : ℝ) ≤ 63 / 64)
  have iL : IntervalIntegrable f volume (1 / 64) (1 / 2) :=
    hfi.mono_set (by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht ⊢
      constructor <;> linarith [ht.1, ht.2])
  have iR : IntervalIntegrable f volume (1 / 2) (63 / 64) :=
    hfi.mono_set (by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht ⊢
      constructor <;> linarith [ht.1, ht.2])
  have href : (∫ s in (1 / 64 : ℝ)..(1 / 2), f s) =
      ∫ s in (1 / 2 : ℝ)..(63 / 64), f s := by
    calc
      _ = ∫ s in (1 / 64 : ℝ)..(1 / 2), f (1 - s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp [f]
        rw [Ua_symm, sub_sub_cancel]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left]
        norm_num
  have hfull : (∫ s in (1 / 64 : ℝ)..(63 / 64), f s) =
      2 * ∫ s in (1 / 64 : ℝ)..(1 / 2), f s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals iL iR, ← href]
    ring
  let T : ℝ → ℝ := fun z => z ^ 4 / (1 + z ^ 4)
  let T' : ℝ → ℝ := fun z => 4 * z ^ 3 / (1 + z ^ 4) ^ 2
  have hTd : ∀ z, HasDerivAt T (T' z) z := by
    intro z
    have hn : 1 + z ^ 4 ≠ 0 := ne_of_gt (by positivity)
    convert (hasDerivAt_pow 4 z).div ((hasDerivAt_pow 4 z).const_add 1) hn using 1 <;>
      dsimp [T, T'] <;> field_simp <;> ring
  have hTc : Continuous T' := by
    dsimp [T']
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z; positivity
  have hmap : MapsTo T (uIcc (71 / 200 : ℝ) 1) (Icc (1 / 64 : ℝ) (63 / 64)) := by
    intro z hz
    rw [uIcc_of_le (by norm_num)] at hz
    have hz0 : 0 ≤ z := by linarith [hz.1]
    have hz4 : (71 / 200 : ℝ) ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ (by norm_num) hz.1 4
    have hz41 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz.2
    dsimp [T]
    constructor
    · rw [le_div_iff₀ (by positivity)]
      norm_num at hz4
      linarith
    · rw [div_le_iff₀ (by positivity)]
      linarith
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (fun z hz => hTd z) hTc.continuousOn (hf.mono (Set.image_subset_iff.mpr hmap))
  have he : (∫ z in (71 / 200 : ℝ)..1, (f ∘ T) z * T' z) =
      ∫ z in (71 / 200 : ℝ)..1, z ^ 6 / (1 + z ^ 4) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le (by norm_num)] at hz
    have hz0 : 0 < z := by linarith [hz.1]
    dsimp [Function.comp_def, f, T, T']
    rw [Ua_quartic_substitution hz0 hz.2]
    ring
  have hT1 : T 1 = 1 / 2 := by norm_num [T]
  rw [he, hT1] at hsub
  have hlow : 1 / 64 ≤ T (71 / 200) := by norm_num [T]
  have hhigh : T (71 / 200) ≤ 1 / 2 := by norm_num [T]
  have hmono : (∫ s in T (71 / 200)..(1 / 2), f s) ≤ ∫ s in (1 / 64 : ℝ)..(1 / 2), f s := by
    apply intervalIntegral.integral_mono_interval hlow hhigh le_rfl _ iL
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [f]
    exact mul_nonneg (Ua_nonneg _) (mul_nonneg (by linarith [hs.1]) (by linarith [hs.2]))
  have hrat := rational_main_integral_lower
  have htwo : (∫ z in (71 / 200 : ℝ)..1, 2 * z ^ 6 / (1 + z ^ 4) ^ 2) =
      2 * ∫ z in (71 / 200 : ℝ)..1, z ^ 6 / (1 + z ^ 4) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  rw [htwo, hsub] at hrat
  change (0.1154 : ℝ) ≤ ∫ s in (1 / 64 : ℝ)..(63 / 64), f s
  rw [hfull]
  linarith


/-- LEAF. Unit U-1556. The truncated main term for `a = 3/2`:
`∫_{x/64}^{63x/64} U_a(t/x) t(x-t) dt ≥ 0.1154 x³`. Plain math: `U_a(s) s(1-s) = (s/(1-s))^{3/4}/4`
for `s ≤ 1/2`, symmetric, and `2 ∫_{1/64}^{1/2} (s/(1-s))^{3/4}/4 ds = 0.115423`
(numerics/U1556/kernel_family_output.txt). -/
theorem main_ge_a {x : ℝ} (hx : 0 < x) :
    0.1154 * x ^ 3 ≤ ∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (t * (x - t)) := by
  have hxne : x ≠ 0 := hx.ne'
  have he : (∫ t in (x / 64)..(63 * x / 64), Ua (t / x) * (t * (x - t))) =
      x ^ 3 * ∫ s in (1 / 64 : ℝ)..(63 / 64), Ua s * (s * (1 - s)) := by
    calc
      _ = ∫ t in (x / 64)..(63 * x / 64),
          x ^ 2 * (Ua (t / x) * ((t / x) * (1 - t / x))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        field_simp
        <;> ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_div (fun s => Ua s * (s * (1 - s))) hxne]
        have ha : x / 64 / x = (1 / 64 : ℝ) := by field_simp
        have hb : 63 * x / 64 / x = (63 / 64 : ℝ) := by field_simp
        rw [ha, hb]
        simp only [smul_eq_mul]
        ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left normalized_main_ge_a (by positivity : 0 ≤ x ^ 3)
  nlinarith only [h]

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
