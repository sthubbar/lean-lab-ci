/-
# Pintz and Althöfer 2026, Theorem 3: the major arc model `V_X²` as a function on the circle

Unit U-1198, T2 FRONTIER, idea I-0080, PC run 20261020T0902Z-22676.

Source: Pintz and Althöfer, arXiv 2610.15559v1, Section 4.3, (4.14): on the arc around `a/q`,
`q ≤ P`, `(a, q) = 1`, `|β| ≤ P/(qX)`, the model is `V_X(a/q + β)² = μ(q)²/φ(q)² (X⁻¹ − 2πiβ)⁻²`,
and its `n`-th Fourier coefficient is
`v_X(n) = Σ_{q≤P} μ(q)² c_q(n)/φ(q)² ∫_{−P/(qX)}^{P/(qX)} e(−nβ)(X⁻¹ − 2πiβ)⁻² dβ`.

What is here, all PROVED unconditional:
* `hArc X δ`, the arc profile `β ↦ 1_{|β| ≤ δ}(X⁻¹ − 2πiβ)⁻²` lifted from `(−1/2, 1/2]` to
  `ℝ/ℤ`; `memLp_hArc`, it is in `L²`; `fourierCoeff_hArc`, its `n`-th coefficient is
  `∫_{−δ}^{δ} e(−nβ)(X⁻¹ − 2πiβ)⁻² dβ` for `δ ≤ 1/2`.
* `fourierCoeff_translate`: translating by `c` multiplies the `n`-th coefficient by `e(−nc)`.
* `ramanujan_neg`: `Σ_{(a,q)=1} e(−na/q) = c_q(n)`.
* `Vfun X P Q`, the model `Σ_{q≤Q} Σ_{(a,q)=1} μ(q)²/φ(q)² hArc(z − a/q)` with `δ_q = P/(qX)`,
  and `fourierCoeff_Vfun`: its `n`-th coefficient is EXACTLY the lab's `vTrunc X P Q (bS n) n`,
  the `v_X(n)` of (4.14), whenever `2P ≤ X`. Arcs may overlap; linearity is all that is used.
* `UpperHalfModel θ`: the concrete L² bound `∫ |F_{x,x²}² − V_x|² ≤ K x^{2a(θ)+1+2η} log x` with
  `V_x = Vfun x P P`, `P = ⌊2√x⌋`, as a Prop, NOT proved. This is the paper's (4.13) after Bessel.
* `upperHalfL2_of_model`, `theorem3_of_model`, `five_eighths_of_model`: Theorem 3 is
  CONDITIONAL ON `UpperHalfModel θ` only, a statement about two explicit functions.

KNOWN mathematics, the paper's own route. AI wrote this Lean code. Binary Goldbach is OPEN.
TRUNCATION FIX, same run, after U-1200: every L² Prop here uses `F_{x,x²} = Σ_{m≤x²}`, not
`Σ_{m≤x}`. With the cut at `x`, the coefficients of `F²` at `n ∈ (x, 2x]` miss the pairs with a
part above `x` and differ from the model's by about `2(n − x)𝔖(n)e^{−n/x}`, so the integral is
`≫ x³` and the Prop would be FALSE for large `x`, since `2a(θ) + 1 < 3`. With the cut at `x²` the
omitted tail `Σ_{m>x²} Λ(m)e^{−m/x}` is `O(x² e^{−x})`, so the Prop is the paper's statement up to
a negligible error; the coefficients on the window are unchanged, `n ≤ x ≤ x²`.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
import LeanLab.PNTPort.Vinogradov.SingSeries

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Model

open Finset Real MeasureTheory AddCircle LeanLab.ExceptionalSet.PintzAlthofer2026
open LeanLab.ExceptionalSet.PintzAlthofer2026Split LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.Routes.R5060

attribute [local instance] Classical.propDecidable

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### The arc profile -/

/-- `(X⁻¹ − 2πiβ)⁻²`. -/
def prof (X β : ℝ) : ℂ := 1 / (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I) ^ 2

theorem den_ne {X : ℝ} (hX : 0 < X) (β : ℝ) :
    (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  exact (ne_of_gt hX) (by simpa using this)

theorem continuous_prof {X : ℝ} (hX : 0 < X) : Continuous (prof X) := by
  unfold prof
  refine Continuous.div continuous_const ?_ (fun β => pow_ne_zero 2 (den_ne hX β))
  fun_prop

theorem norm_prof_le {X : ℝ} (hX : 0 < X) (β : ℝ) : ‖prof X β‖ ≤ X ^ 2 := by
  unfold prof
  set z := (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I)
  have hz : 1 / X ≤ ‖z‖ := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h2 : z.re = 1 / X := by simp [z]
    rw [h2, abs_of_pos (by positivity)] at h1; exact h1
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  rw [norm_div, norm_one, norm_pow, div_le_iff₀ (by positivity)]
  have : 1 ≤ X * ‖z‖ := by rw [div_le_iff₀ hX] at hz; linarith
  nlinarith

/-- The arc profile on `ℝ`: `1_{(−δ, δ]}(β) (X⁻¹ − 2πiβ)⁻²`. -/
def gArc (X δ : ℝ) : ℝ → ℂ := Set.indicator (Set.Ioc (-δ) δ) (prof X)

/-- The arc profile on the circle, lifted from `(−1/2, 1/2]`. -/
def hArc (X δ : ℝ) : 𝕋 → ℂ := AddCircle.liftIoc 1 (-(1 / 2)) (gArc X δ)

theorem memLp_gArc {X : ℝ} (hX : 0 < X) (δ : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    MemLp (gArc X δ) 2 μ := by
  refine MemLp.of_bound ?_ (X ^ 2) (Filter.Eventually.of_forall fun β => ?_)
  · exact ((continuous_prof hX).aestronglyMeasurable).indicator measurableSet_Ioc
  · unfold gArc
    by_cases h : β ∈ Set.Ioc (-δ) δ
    · rw [Set.indicator_of_mem h]; exact norm_prof_le hX β
    · rw [Set.indicator_of_notMem h, norm_zero]; positivity

theorem memLp_hArc {X : ℝ} (hX : 0 < X) (δ : ℝ) : MemLp (hArc X δ) 2 haarAddCircle := by
  have h : MemLp (gArc X δ) 2 (volume.restrict (Set.Ioc (-(1 / 2)) (-(1 / 2) + 1))) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1))) := by
      refine ⟨?_⟩; rw [Measure.restrict_apply_univ]; simp
    exact memLp_gArc hX δ _
  exact h.memLp_liftIoc.haarAddCircle

/-- `e(−nβ)(X⁻¹ − 2πiβ)⁻²` is the lab's `mInt X n β`. -/
theorem fourier_mul_prof (X : ℝ) (n : ℕ) (β : ℝ) :
    fourier (-(n : ℤ)) (β : 𝕋) * prof X β =
      LeanLab.ExceptionalSet.PintzAlthofer2026Beta.mInt X n β := by
  rw [fourier_coe_apply]
  unfold LeanLab.ExceptionalSet.PintzAlthofer2026Beta.mInt prof
  congr 2
  push_cast; ring

/-- **`fourierCoeff_hArc`**: for `0 ≤ δ ≤ 1/2`, the `n`-th coefficient of the arc profile is
`∫_{(−δ, δ]} e(−nβ)(X⁻¹ − 2πiβ)⁻² dβ`. -/
theorem fourierCoeff_hArc (X δ : ℝ) (hδ : δ ≤ 1 / 2) (n : ℕ) :
    fourierCoeff (hArc X δ) n =
      ∫ β in Set.Ioc (-δ) δ, LeanLab.ExceptionalSet.PintzAlthofer2026Beta.mInt X n β := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-(1 / 2))]
  have hcongr : ∫ x in (-(1 / 2) : ℝ)..(-(1 / 2) + 1), fourier (-(n : ℤ)) (x : 𝕋) • hArc X δ x =
      ∫ x in (-(1 / 2) : ℝ)..(-(1 / 2) + 1),
        Set.indicator (Set.Ioc (-δ) δ) (LeanLab.ExceptionalSet.PintzAlthofer2026Beta.mInt X n) x := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hx
    unfold hArc
    rw [AddCircle.liftIoc_coe_apply hx, smul_eq_mul]
    unfold gArc
    by_cases h : x ∈ Set.Ioc (-δ) δ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, fourier_mul_prof]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [hcongr, intervalIntegral.integral_of_le (by norm_num),
    setIntegral_indicator measurableSet_Ioc]
  have hsub : Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) ∩ Set.Ioc (-δ) δ = Set.Ioc (-δ) δ := by
    apply Set.inter_eq_right.2
    intro x hx
    simp only [Set.mem_Ioc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  rw [hsub]
  simp

/-! ### Translation and the Ramanujan sum -/

theorem fourier_add_arg (n : ℤ) (x y : 𝕋) : fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- **`fourierCoeff_translate`**: `(f(· − c))^(n) = e(−nc) f̂(n)`. -/
theorem fourierCoeff_translate (f : 𝕋 → ℂ) (c : 𝕋) (n : ℤ) :
    fourierCoeff (fun z => f (z - c)) n = fourier (-n) c * fourierCoeff f n := by
  unfold fourierCoeff
  have h := integral_sub_right_eq_self (μ := (haarAddCircle : Measure 𝕋))
    (fun w => fourier (-n) (w + c) • f w) c
  simp only [sub_add_cancel] at h
  rw [h, ← smul_eq_mul, ← integral_smul]
  congr 1; ext w
  rw [fourier_add_arg, smul_eq_mul, smul_eq_mul, smul_eq_mul]; ring

/-- **`ramanujan_neg`**: `Σ_{a<q, (a,q)=1} e(−na/q) = c_q(n)`. -/
theorem ramanujan_neg {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), fourier (-(n : ℤ)) (((a : ℝ) / q : ℝ) : 𝕋)
      = (LeanLab.HeathBrown1985.ramanujan q n : ℂ) := by
  have h := LeanLab.PNTPort.Vinogradov.ramanujan_sum hq n
  have hc := congrArg (starRingEnd ℂ) h
  rw [map_sum, Complex.conj_ofReal] at hc
  rw [← hc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fourier_coe_apply]
  unfold LeanLab.PNTPort.LargeSieve.e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

/-! ### The model `V_X²` on the circle -/

/-- The model `Σ_{q≤Q} Σ_{(a,q)=1} μ(q)²/φ(q)² hArc_{P/(qX)}(z − a/q)`. -/
def Vfun (X P : ℝ) (Q : ℕ) (z : 𝕋) : ℂ :=
  ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))

theorem memLp_translate {f : 𝕋 → ℂ} (hf : MemLp f 2 haarAddCircle) (c : 𝕋) :
    MemLp (fun z => f (z - c)) 2 haarAddCircle := by
  have hmp : MeasurePreserving (fun z : 𝕋 => z - c) haarAddCircle haarAddCircle := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right (haarAddCircle : Measure 𝕋) (-c)
  exact hf.comp_measurePreserving hmp

theorem memLp_term {X : ℝ} (hX : 0 < X) (k : ℂ) (δ : ℝ) (c : 𝕋) :
    MemLp (fun z => k * hArc X δ (z - c)) 2 haarAddCircle :=
  (memLp_translate (memLp_hArc hX δ) c).const_mul k

theorem memLp_Vfun {X : ℝ} (hX : 0 < X) (P : ℝ) (Q : ℕ) : MemLp (Vfun X P Q) 2 haarAddCircle := by
  have h1 : Vfun X P Q = ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (fun z => (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))) := by
    ext z; simp [Vfun, Finset.sum_apply]
  rw [h1]
  exact memLp_finset_sum' _ fun q _ => memLp_finset_sum' _ fun a _ => memLp_term hX _ _ _

/-- **`fourierCoeff_Vfun`**: for `0 < X`, `0 ≤ P`, `2P ≤ X`, the `n`-th Fourier coefficient of
the model is EXACTLY `vTrunc X P Q (bS n) n`, the `v_X(n)` of (4.14). -/
theorem fourierCoeff_Vfun {X P : ℝ} (hX : 0 < X) (hP : 0 ≤ P) (h2P : 2 * P ≤ X) (Q n : ℕ) :
    fourierCoeff (Vfun X P Q) n =
      LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc X P Q (fun q => ((bS n q : ℝ) : ℂ)) n := by
  have h1 : Vfun X P Q = ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (fun z => (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))) := by
    ext z; simp [Vfun, Finset.sum_apply]
  have hint : ∀ (k : ℂ) (δ : ℝ) (c : 𝕋),
      Integrable (fun z => k * hArc X δ (z - c)) haarAddCircle :=
    fun k δ c => (memLp_term hX k δ c).integrable one_le_two
  set F : ℕ → 𝕋 → ℂ := fun q => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (fun z => (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))) with hF
  rw [h1, fourierCoeff.sum (Icc 1 Q) F (fun q _ => by
    rw [hF]; exact integrable_finset_sum' _ fun a _ => hint _ _ _)]
  rw [Finset.sum_apply]
  unfold LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hδ : P / (q * X) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [hF]
  dsimp only
  rw [fourierCoeff.sum _ _ (fun a _ => hint _ _ _), Finset.sum_apply]
  have hterm : ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      fourierCoeff (fun z => (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        hArc X (P / (q * X)) (z - (((a : ℝ) / q : ℝ) : 𝕋))) n =
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        (fourier (-(n : ℤ)) (((a : ℝ) / q : ℝ) : 𝕋) *
          ∫ β in Set.Ioc (-(P / (q * X))) (P / (q * X)),
            LeanLab.ExceptionalSet.PintzAlthofer2026Beta.mInt X n β) := by
    intro a _
    rw [fourierCoeff.const_mul, fourierCoeff_translate, fourierCoeff_hArc X _ hδ n]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_mul, ramanujan_neg hq1 n,
    bS_apply hq1 n]
  push_cast
  ring

/-! ### Theorem 3 from the concrete L² bound -/

theorem two_Ppaper_le (x : ℕ) (hx : 16 ≤ x) : 2 * Ppaper x ≤ x := by
  unfold Ppaper
  set s := Nat.sqrt (4 * x)
  have h1 : s * s ≤ 4 * x := Nat.sqrt_le (4 * x)
  by_contra h
  push_neg at h
  have h2 : (x + 1) * (x + 1) ≤ (2 * s) * (2 * s) := Nat.mul_le_mul h h
  nlinarith

/-- **The concrete upper half**, the paper's (4.13) after Bessel, as a Prop, NOT proved: with the
explicit `F_{x,x²}` and the explicit model `V_x = Vfun x P P`, `P = ⌊2√x⌋`,
`∫_{ℝ/ℤ} |F_{x,x²}² − V_x|² ≤ K x^{2a(θ)+1+2η} log x` for every `η > 0` and large `x`. -/
def UpperHalfModel (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x →
    ∫ t, ‖FX x (x ^ 2) t ^ 2 - Vfun x (Ppaper x) (Ppaper x) t‖ ^ 2 ∂haarAddCircle ≤
      K * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x

theorem upperHalfL2_of_model {θ : ℝ} (hM : UpperHalfModel θ) : UpperHalfL2 θ := by
  intro η hη
  obtain ⟨K, X0, hK⟩ := hM η hη
  refine ⟨K, max X0 16, fun x hx => ⟨Vfun x (Ppaper x) (Ppaper x), ?_, ?_, ?_⟩⟩
  · have hx0 : (0 : ℝ) < x := by
      have : 16 ≤ x := le_trans (le_max_right _ _) hx
      exact_mod_cast (show 0 < x by omega)
    exact memLp_Vfun hx0 _ _
  · intro n _
    have hx16 : 16 ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have h2 : 2 * (Ppaper x : ℝ) ≤ x := by exact_mod_cast two_Ppaper_le x hx16
    rw [fourierCoeff_Vfun hx0 (Nat.cast_nonneg _) h2]
    rfl
  · exact hK x (le_trans (le_max_left _ _) hx)

/-- Theorem 3 of Pintz-Althöfer, CONDITIONAL ON `UpperHalfModel θ` only. -/
theorem theorem3_of_model {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) (hM : UpperHalfModel θ) :
    ∀ ε : ℝ, 0 < ε → PowerBound (g θ + ε) :=
  theorem3_of_L2 h1 h2 (upperHalfL2_of_model hM)

/-- θ = 5/8, CONDITIONAL ON `UpperHalfModel (5/8)` only: `E(X) ≪ X^{25/44+ε}`. -/
theorem five_eighths_of_model (hM : UpperHalfModel (5 / 8)) :
    ∀ ε : ℝ, 0 < ε → PowerBound (25 / 44 + ε) :=
  five_eighths_of_L2 (upperHalfL2_of_model hM)

/-! ### Vacuity -/

/-- The hypothesis `2P ≤ X` of `fourierCoeff_Vfun` holds at the paper's truncation: `x = 100`,
`P = 20`. -/
example : 2 * Ppaper 100 ≤ 100 := two_Ppaper_le 100 (by norm_num)

/-- The arc profile is not zero: at `β = 0` it is `X²`. -/
example : prof 2 0 = 4 := by
  unfold prof; push_cast; norm_num

end

end LeanLab.ExceptionalSet.PintzAlthofer2026Model
