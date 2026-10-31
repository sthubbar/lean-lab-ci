/-
# Pintz and Althöfer 2026, (4.13) from (4.11) and (4.12)

Unit U-1201, T2 FRONTIER, idea I-0080, PC run 20261020T0902Z-22676.

Source: arXiv 2610.15559v1, Section 4.3, read on the page this run: (4.11) is the global estimate
`‖F_X − V_X‖_∞ ≪ X^{a(θ)+η}`; (4.12) is `‖F_X‖₂² ≪ X log X`, `‖V_X‖₂² ≪ X log X`; and
"Therefore ∫₀¹ |F_X² − V_X²|² ≤ ‖F_X − V_X‖_∞² ‖F_X + V_X‖₂² ≪ X^{2a(θ)+1+2η} log X", (4.13).

What is here, all PROVED unconditional:
* `parseval_trig`: `∫ |Σ_{m≤M} a_m e(mt)|² = Σ_{m≤M} |a_m|²`.
* `int_FX_sq_le`: `∫ |F_{x,x²}|² ≤ 4x(log x)²`, for `x ≥ 2`. The paper has `X log X` by Chebyshev;
  the lab uses `Λ(m) ≤ 2 log x` and a geometric sum, and pays one `log`, absorbed into `X^η`.
* `int_norm_prof_le`: `∫_{(−δ,δ]} |X⁻¹ − 2πiβ|⁻² dβ ≤ πX`, by the arctan integral.
* `int_norm_hArc`, `int_norm_Vfun_le`: `∫ |V_X|² = ∫ |Vfun| ≤ πX Σ_{q≤Q} 1/φ(q)`, the paper's (4.12)
  for `V_X`.
* `SupBound θ`, NOT proved: `sup_z |F_{x,x²}(z) − V_x(z)| ≤ K x^{a(θ)+η}`, `V_x` the paper's linear
  model at `P = ⌊x^{1/3}⌋`. This is the paper's (4.11).
* `model3_of_sup`: `SupBound θ → UpperHalfModel3 θ`, the paper's step (4.11), (4.12) ⇒ (4.13).
* `theorem3_of_sup`, `five_eighths_of_sup`: Theorem 3 CONDITIONAL ON the sup bound (4.11) only.

KNOWN mathematics, the paper's route. AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Linear

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Sup

open Finset Real MeasureTheory AddCircle LeanLab.ExceptionalSet.PintzAlthofer2026
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.PintzAlthofer2026Cube LeanLab.ExceptionalSet.PintzAlthofer2026Linear

attribute [local instance] Classical.propDecidable

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Parseval for trigonometric polynomials -/

theorem fourierCoeff_trig_int (a : ℕ → ℂ) (M : ℕ) (i : ℤ) :
    fourierCoeff (trig a M) i = ∑ m ∈ range (M + 1), if i = (m : ℤ) then a m else 0 := by
  have : trig a M = fun t : 𝕋 => ∑ m ∈ range (M + 1), a m * fourier (m : ℤ) t := rfl
  rw [this, fourierCoeff_sum_monomial]

/-- **`parseval_trig`**: `∫ |Σ_{m≤M} a_m e(mt)|² = Σ_{m≤M} |a_m|²`. -/
theorem parseval_trig (a : ℕ → ℂ) (M : ℕ) :
    ∫ t, ‖trig a M t‖ ^ 2 ∂haarAddCircle = ∑ m ∈ range (M + 1), ‖a m‖ ^ 2 := by
  have hmem : MemLp (trig a M) 2 haarAddCircle :=
    (continuous_trig a M).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set g := hmem.toLp (trig a M)
  have hcoef : fourierCoeff (g : 𝕋 → ℂ) = fourierCoeff (trig a M) :=
    fourierCoeff_congr_ae (MemLp.coeFn_toLp hmem)
  have hint : ∫ t, ‖(g : 𝕋 → ℂ) t‖ ^ 2 ∂haarAddCircle = ∫ t, ‖trig a M t‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hmem] with t ht
    rw [ht]
  have h := hasSum_sq_fourierCoeff g
  rw [hcoef, hint] at h
  set S : Finset ℤ := (range (M + 1)).image (fun m : ℕ => (m : ℤ))
  have hzero : ∀ i ∉ S, ‖fourierCoeff (trig a M) i‖ ^ 2 = 0 := by
    intro i hi
    rw [fourierCoeff_trig_int, Finset.sum_eq_zero, norm_zero]
    · norm_num
    · intro m hm
      rw [if_neg]
      intro him; exact hi (Finset.mem_image.2 ⟨m, hm, him.symm⟩)
  have h2 : HasSum (fun i : ℤ => ‖fourierCoeff (trig a M) i‖ ^ 2)
      (∑ i ∈ S, ‖fourierCoeff (trig a M) i‖ ^ 2) := hasSum_sum_of_ne_finset_zero hzero
  rw [h.unique h2, Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [fourierCoeff_trig a M m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))]

/-! ### (4.12) for `F` -/

theorem geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ m ∈ range N, r ^ m ≤ 1 / (1 - r) := by
  rw [geom_sum_eq (ne_of_lt h1)]
  have hr : 0 < 1 - r := by linarith
  have heq : (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) := by
    rw [div_eq_div_iff (by linarith) hr.ne']; ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ hr.le
  have : 0 ≤ r ^ N := pow_nonneg h0 N
  linarith

/-- **`int_FX_sq_le`**: `∫ |F_{x,x²}|² ≤ 4x(log x)²` for `x ≥ 2`. -/
theorem int_FX_sq_le (x : ℕ) (hx : 2 ≤ x) :
    ∫ t, ‖FX x (x ^ 2) t‖ ^ 2 ∂haarAddCircle ≤ 4 * x * Real.log x ^ 2 := by
  unfold FX
  rw [parseval_trig]
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  set r := Real.exp (-2 / x)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  -- each term
  have hterm : ∀ m ∈ range (x ^ 2 + 1), ‖aF x m‖ ^ 2 ≤ (2 * Real.log x) ^ 2 * r ^ m := by
    intro m hm
    have hm' : m ≤ x ^ 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    unfold aF
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
    have hΛ : ArithmeticFunction.vonMangoldt m ≤ 2 * Real.log x := by
      refine (ArithmeticFunction.vonMangoldt_le_log).trans ?_
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp; positivity
      · have : Real.log m ≤ Real.log ((x : ℝ) ^ 2) := by
          apply Real.log_le_log (by exact_mod_cast h)
          exact_mod_cast hm'
        rw [Real.log_pow] at this; push_cast at this; linarith
    have hexp : Real.exp (-(m : ℝ) / x) ^ 2 = r ^ m := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; field_simp; ring
    rw [hexp]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 m)
    exact pow_le_pow_left₀ hΛ0 hΛ 2
  -- the geometric sum
  have hu : 2 / (x : ℝ) ≤ 1 := by rw [div_le_one hx0]; exact_mod_cast hx
  have hr1 : r ≤ 1 / (1 + 2 / x) := by
    have := Real.add_one_le_exp (2 / x)
    rw [le_div_iff₀ (by positivity)]
    have h2 : r * Real.exp (2 / x) = 1 := by
      rw [← Real.exp_add]; simp [neg_div]
    nlinarith [Real.exp_pos (2 / (x : ℝ))]
  have hgap : 1 / (x : ℝ) ≤ 1 - r := by
    have : 1 / (1 + 2 / (x : ℝ)) ≤ 1 - 1 / x := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 - 1 / (x : ℝ)) * (1 + 2 / x) = 1 + 1 / x - 2 / x ^ 2 := by field_simp; ring
      rw [this]
      have : 2 / (x : ℝ) ^ 2 ≤ 1 / x := by
        rw [div_le_div_iff₀ (by positivity) hx0]
        have : (2 : ℝ) ≤ x := by exact_mod_cast hx
        nlinarith
      linarith
    linarith
  have hrlt : r < 1 := by
    have : 0 < 1 / (x : ℝ) := by positivity
    linarith
  have hgeom : ∑ m ∈ range (x ^ 2 + 1), r ^ m ≤ x := by
    refine (geom_le hr0 hrlt _).trans ?_
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hgap hx0.le
    rw [mul_one_div_cancel hx0.ne'] at this
    linarith
  calc ∑ m ∈ range (x ^ 2 + 1), ‖aF x m‖ ^ 2
      ≤ ∑ m ∈ range (x ^ 2 + 1), (2 * Real.log x) ^ 2 * r ^ m := Finset.sum_le_sum hterm
    _ = (2 * Real.log x) ^ 2 * ∑ m ∈ range (x ^ 2 + 1), r ^ m := by rw [Finset.mul_sum]
    _ ≤ (2 * Real.log x) ^ 2 * x := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 4 * x * Real.log x ^ 2 := by ring

/-! ### (4.12) for `V` -/

theorem norm_prof_le' {X : ℝ} (hX : 0 < X) (β : ℝ) : ‖prof X β‖ ≤ X ^ 2 * (1 + (X * β) ^ 2)⁻¹ := by
  unfold prof
  set z := (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I)
  have hz2 : ‖z‖ ^ 2 = (1 / X) ^ 2 + (2 * π * β) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [z]; ring
  have hpos : 0 < (1 / X) ^ 2 + (2 * π * β) ^ 2 := by positivity
  rw [norm_div, norm_one, norm_pow, hz2]
  rw [div_le_iff₀ hpos]
  have hpi : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have h1 : 0 < 1 + (X * β) ^ 2 := by positivity
  rw [← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ h1]
  have : X ^ 2 * ((1 / X) ^ 2 + (2 * π * β) ^ 2) = 1 + 4 * π ^ 2 * (X * β) ^ 2 := by
    field_simp; ring
  rw [this]
  nlinarith [sq_nonneg (X * β)]

/-- **`int_norm_prof_le`**: `∫_{(−δ,δ]} |X⁻¹ − 2πiβ|⁻² dβ ≤ πX`. -/
theorem int_norm_prof_le {X : ℝ} (hX : 0 < X) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ β in Set.Ioc (-δ) δ, ‖prof X β‖ ≤ π * X := by
  rw [← intervalIntegral.integral_of_le (by linarith)]
  have hc1 : Continuous fun β => ‖prof X β‖ := (continuous_prof hX).norm
  have hc2 : Continuous fun β : ℝ => X ^ 2 * (1 + (X * β) ^ 2)⁻¹ := by
    refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun β => ?_)
    positivity
  have hmono : ∫ β in (-δ)..δ, ‖prof X β‖ ≤ ∫ β in (-δ)..δ, X ^ 2 * (1 + (X * β) ^ 2)⁻¹ :=
    intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) fun β _ => norm_prof_le' hX β
  have hval : ∫ β in (-δ)..δ, X ^ 2 * (1 + (X * β) ^ 2)⁻¹ =
      X * (Real.arctan (X * δ) - Real.arctan (X * -δ)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u => (1 + u ^ 2)⁻¹) hX.ne',
      integral_inv_one_add_sq, smul_eq_mul]
    field_simp
  have h1 := Real.arctan_lt_pi_div_two (X * δ)
  have h2 := Real.neg_pi_div_two_lt_arctan (X * -δ)
  rw [hval] at hmono
  nlinarith

/-- `∫ |hArc| = ∫_{(−δ,δ]} |prof|` for `0 ≤ δ ≤ 1/2`. -/
theorem int_norm_hArc {X δ : ℝ} (hδ : δ ≤ 1 / 2) :
    ∫ z, ‖hArc X δ z‖ ∂haarAddCircle = ∫ β in Set.Ioc (-δ) δ, ‖prof X β‖ := by
  rw [integral_haarAddCircle, inv_one, one_smul]
  have hfun : (fun z => ‖hArc X δ z‖) =
      AddCircle.liftIoc 1 (-(1 / 2)) (fun β => ‖gArc X δ β‖) := rfl
  rw [hfun, AddCircle.integral_liftIoc_eq_intervalIntegral,
    intervalIntegral.integral_of_le (by norm_num)]
  have hind : (fun β => ‖gArc X δ β‖) = Set.indicator (Set.Ioc (-δ) δ) (fun β => ‖prof X β‖) := by
    ext β; unfold gArc; rw [norm_indicator_eq_indicator_norm]
  rw [hind, setIntegral_indicator measurableSet_Ioc]
  have hsub : Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) ∩ Set.Ioc (-δ) δ = Set.Ioc (-δ) δ := by
    apply Set.inter_eq_right.2
    intro x hx
    simp only [Set.mem_Ioc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  rw [hsub]

theorem card_reduced (q : ℕ) : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient]
  congr 1
  ext a; simp [Nat.coprime_comm]

/-- **`int_norm_Vfun_le`**: `∫ |Vfun| ≤ πX Σ_{q≤Q} 1/φ(q)` when `0 ≤ P` and `2P ≤ X`. -/
theorem int_norm_Vfun_le {X P : ℝ} (hX : 0 < X) (hP : 0 ≤ P) (h2P : 2 * P ≤ X) (Q : ℕ) :
    ∫ z, ‖Vfun X P Q z‖ ∂haarAddCircle ≤ π * X * ∑ q ∈ Icc 1 Q, (1 : ℝ) / q.totient := by
  set c : ℕ → ℝ := fun q => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2
  have hpt : ∀ z, ‖Vfun X P Q z‖ ≤ ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      c q * ‖hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))‖ := by
    intro z
    unfold Vfun
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hintT : ∀ (q a : ℕ), Integrable
      (fun z => c q * ‖hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))‖) haarAddCircle :=
    fun q a => ((memLp_translate (memLp_hArc hX _) _).integrable one_le_two).norm.const_mul _
  have hRint : Integrable (fun z => ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      c q * ‖hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))‖) haarAddCircle :=
    integrable_finset_sum _ fun q _ => integrable_finset_sum _ fun a _ => hintT q a
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hRint
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_finset_sum _ fun q _ => integrable_finset_sum _ fun a _ => hintT q a]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hδ : P / (q * X) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hδ0 : 0 ≤ P / (q * X) := by positivity
  rw [integral_finset_sum _ fun a _ => hintT q a]
  have heach : ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ∫ z, c q * ‖hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))‖ ∂haarAddCircle ≤
        c q * (π * X) := by
    intro a _
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := integral_sub_right_eq_self (μ := (haarAddCircle : Measure 𝕋))
      (fun z => ‖hArc X (P / (q * X)) z‖) (((a : ℝ) / q : ℝ) : 𝕋)
    rw [this, int_norm_hArc hδ]
    exact int_norm_prof_le hX hδ0
  refine (Finset.sum_le_sum heach).trans ?_
  rw [Finset.sum_const, card_reduced, nsmul_eq_mul]
  have htot : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hμ : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := q)
    have : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by exact_mod_cast h
    nlinarith [abs_nonneg (ArithmeticFunction.moebius q : ℝ), sq_abs (ArithmeticFunction.moebius q : ℝ)]
  simp only [c]
  rw [show (q.totient : ℝ) * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (π * X))
      = (ArithmeticFunction.moebius q : ℝ) ^ 2 * (π * X * (1 / q.totient)) by field_simp]
  have : 0 ≤ π * X * (1 / (q.totient : ℝ)) := by positivity
  nlinarith

/-! ### (4.11) ⇒ (4.13) -/

/-- **The paper's (4.11)**, as a Prop, NOT proved: for every `η > 0` and large `x`,
`sup_z |F_{x,x²}(z) − V_x(z)| ≤ K x^{a(θ)+η}`, with `V_x` the linear model at `P = ⌊x^{1/3}⌋`. -/
def SupBound (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → ∀ z : 𝕋,
    ‖FX x (x ^ 2) z - Vlin x (P3 x) (P3 x) z‖ ≤ K * (x : ℝ) ^ (a θ + η)

set_option maxHeartbeats 1000000 in
/-- **`model3_of_sup`**: (4.11), with (4.12) proved here, gives (4.13). -/
theorem model3_of_sup {θ : ℝ} (hS : SupBound θ) : UpperHalfModel3 θ := by
  intro η hη
  obtain ⟨K, X0, hK⟩ := hS (η / 2) (by positivity)
  obtain ⟨C, hC, hCsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  set K' := K ^ 2 * (8 / η + 4 * π * C)
  refine ⟨K', max X0 9, fun x hx => ?_⟩
  have hx9 : 9 ≤ x := le_trans (le_max_right _ _) hx
  have hxX0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  set F := FX x (x ^ 2)
  set V := Vlin x (P3 x) (P3 x)
  set W := Vfun x (P3 x) (P3 x)
  set S := K * (x : ℝ) ^ (a θ + η / 2)
  have hVW : ∀ z, V z ^ 2 = W z := fun z => Vlin_sq_P3 x hx9 z
  have hFV : ∀ z, ‖F z - V z‖ ≤ S := hK x hxX0
  have hS0 : 0 ≤ S := le_trans (norm_nonneg _) (hFV 0)
  -- pointwise
  have hpt : ∀ z, ‖F z ^ 2 - W z‖ ^ 2 ≤ S ^ 2 * (2 * ‖F z‖ ^ 2 + 2 * ‖W z‖) := by
    intro z
    have hfac : F z ^ 2 - W z = (F z - V z) * (F z + V z) := by rw [← hVW z]; ring
    rw [hfac, norm_mul, mul_pow]
    have h1 : ‖F z - V z‖ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hFV z) 2
    have h2 : ‖F z + V z‖ ^ 2 ≤ 2 * ‖F z‖ ^ 2 + 2 * ‖W z‖ := by
      have hn := norm_add_le (F z) (V z)
      have hVn : ‖V z‖ ^ 2 = ‖W z‖ := by rw [← hVW z, norm_pow]
      nlinarith [norm_nonneg (F z + V z), norm_nonneg (F z), norm_nonneg (V z),
        sq_nonneg (‖F z‖ - ‖V z‖)]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  -- integrability of the right side
  have hFint : Integrable (fun z => ‖F z‖ ^ 2) haarAddCircle :=
    ((continuous_trig _ _).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hWint : Integrable (fun z => ‖W z‖) haarAddCircle :=
    ((memLp_Vfun hx0 _ _).integrable one_le_two).norm
  have hRint : Integrable (fun z => S ^ 2 * (2 * ‖F z‖ ^ 2 + 2 * ‖W z‖)) haarAddCircle :=
    ((hFint.const_mul 2).add (hWint.const_mul 2)).const_mul _
  have hint := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) hRint
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_add (hFint.const_mul 2) (hWint.const_mul 2),
    integral_const_mul, integral_const_mul] at hint
  -- the two L² bounds
  have hF2 := int_FX_sq_le x (by omega)
  have h2P : 2 * (P3 x : ℝ) ≤ x := by exact_mod_cast two_P3_le x (by omega)
  have hW1 := int_norm_Vfun_le hx0 (Nat.cast_nonneg (P3 x)) h2P (P3 x)
  have hsum := hCsum (P3 x)
  have hlogx : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have : (9 : ℝ) ≤ x := by exact_mod_cast hx9
    linarith
  have hlogP : Real.log (P3 x) ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos (P3 x) with h | h
    · rw [h]; simp; linarith
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast P3_le x (by omega))
  have hW2 : ∫ z, ‖W z‖ ∂haarAddCircle ≤ π * x * (C * (2 * Real.log x)) := by
    refine hW1.trans (mul_le_mul_of_nonneg_left (hsum.trans ?_) (by positivity))
    apply mul_le_mul_of_nonneg_left _ hC.le; linarith
  have hlogeta : Real.log x ≤ (x : ℝ) ^ η / η := Real.log_le_rpow_div hx0.le hη
  have hxeta : (1 : ℝ) ≤ (x : ℝ) ^ η := Real.one_le_rpow hx1 hη.le
  -- assemble
  have hS2 : S ^ 2 = K ^ 2 * (x : ℝ) ^ (2 * a θ + η) := by
    simp only [S]
    rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]; congr 2; push_cast; ring
  have hpow : (x : ℝ) ^ (2 * a θ + η) * x * (x : ℝ) ^ η = (x : ℝ) ^ (2 * a θ + 1 + 2 * η) := by
    calc (x : ℝ) ^ (2 * a θ + η) * x * (x : ℝ) ^ η
        = (x : ℝ) ^ (2 * a θ + η) * (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ η := by rw [Real.rpow_one]
      _ = (x : ℝ) ^ (2 * a θ + η + 1 + η) := by rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      _ = (x : ℝ) ^ (2 * a θ + 1 + 2 * η) := by congr 1; ring
  have hlogx0 : 0 ≤ Real.log x := by linarith
  have hB : 2 * ∫ z, ‖F z‖ ^ 2 ∂haarAddCircle + 2 * ∫ z, ‖W z‖ ∂haarAddCircle ≤
      (8 / η + 4 * π * C) * x * (x : ℝ) ^ η * Real.log x := by
    have e1 : 2 * (4 * x * Real.log x ^ 2) ≤ 8 / η * x * (x : ℝ) ^ η * Real.log x := by
      have : Real.log x ^ 2 ≤ (x : ℝ) ^ η / η * Real.log x := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hlogeta hlogx0
      have h8 : 8 / η * x * (x : ℝ) ^ η * Real.log x = 8 * x * ((x : ℝ) ^ η / η * Real.log x) := by
        field_simp
      rw [h8]; nlinarith
    have e2 : 2 * (π * x * (C * (2 * Real.log x))) ≤ 4 * π * C * x * (x : ℝ) ^ η * Real.log x := by
      have : 0 ≤ 4 * π * C * x * Real.log x := by positivity
      nlinarith
    nlinarith
  calc ∫ t, ‖FX x (x ^ 2) t ^ 2 - Vfun x (P3 x) (P3 x) t‖ ^ 2 ∂haarAddCircle
      ≤ S ^ 2 * (2 * ∫ z, ‖F z‖ ^ 2 ∂haarAddCircle + 2 * ∫ z, ‖W z‖ ∂haarAddCircle) := hint
    _ ≤ S ^ 2 * ((8 / η + 4 * π * C) * x * (x : ℝ) ^ η * Real.log x) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = K' * ((x : ℝ) ^ (2 * a θ + η) * x * (x : ℝ) ^ η) * Real.log x := by
        rw [hS2]; simp only [K']; ring
    _ = K' * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x := by rw [hpow]

/-- Theorem 3 of Pintz-Althöfer, CONDITIONAL ON the paper's sup bound (4.11), `SupBound θ`, only. -/
theorem theorem3_of_sup {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) (hS : SupBound θ) :
    ∀ ε : ℝ, 0 < ε → PowerBound (g θ + ε) :=
  theorem3_of_model3 h1 h2 (model3_of_sup hS)

/-- θ = 5/8, CONDITIONAL ON `SupBound (5/8)` only: `E(X) ≪ X^{25/44+ε}`. -/
theorem five_eighths_of_sup (hS : SupBound (5 / 8)) :
    ∀ ε : ℝ, 0 < ε → PowerBound (25 / 44 + ε) :=
  five_eighths_of_model3 (model3_of_sup hS)

/-! ### Vacuity -/

/-- `parseval_trig` on `1 + e(t)`: `∫ |1 + e(t)|² = 2`. -/
example : ∫ t, ‖trig (fun _ => (1 : ℂ)) 1 t‖ ^ 2 ∂haarAddCircle = 2 := by
  rw [parseval_trig]; simp [Finset.sum_range_succ]

end

end LeanLab.ExceptionalSet.PintzAlthofer2026Sup
