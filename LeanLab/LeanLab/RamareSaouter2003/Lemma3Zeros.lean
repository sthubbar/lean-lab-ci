import Mathlib
import LeanLab.RamareSaouter2003.Theorem4JSplit

/-!
# Ramaré-Saouter 2003, Lemmas 2 and 3 for a zero family

P0099, unit U-6762, session 20261020T2217Z-cloud52. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

A zero family is an index type `ι` with ordinates `γ i` and real parts `β i`, each zero listed
with its multiplicity. `ZsF γ β m T x = Σ'_{|γ i| > T} x^(β i)/|γ i|^(m+1)` is the zero sum of
Lemma 3 of p. 15.

* `Lemma1Count γ`: Lemma 1 of p. 14, read as counts over any finite set of the zeros, both
  signs of the ordinate: `#{T < |γ| ≤ t} ≤ 2 ((M t + E t) - (M T - E T))` for `10^3 ≤ T ≤ t`,
  `M t = (t/2π) log(t/2π) - t/2π + 7/8`, `E t = 0.67 log(t/2π)`. CITED, Rosser 1941 Theorem 19
  through Lemma 1; for the zeros of ζ it is `2 (N t - N T)` by the symmetry `ρ ↦ conj ρ`.
* `lemma2_upper`: Lemma 2 of p. 14, upper half, over any finite set:
  `Σ_{|γ| > T} 1/|γ|^(m+1) ≤ L2 m T / T^m` with
  `L2 m T = (log(T/2π) + 1/m)/(mπ) + (1.34/T)(2 log(T/2π) + 1)`.
  PROVED CONDITIONAL ON `Lemma1Count`, by the paper's partial summation done as a layer cake
  on `(T, R]`: the antiderivative `F` of `(m+1) H(t)/t^(m+2)`, `H` the count majorant, gives
  `H(T)/T^(m+1) = 2.68 log(T/2π)/T^(m+1)` plus the main term plus `1.34/((m+1) T^(m+1))`.
* `lemma3_of`: `Lemma3Bound (ZsF γ β) T0` of `Theorem4JSplit.lean`, Lemma 3 as printed, PROVED
  CONDITIONAL ON `Lemma1Count γ`, RH to height `T0` for the family, that is `β i = 1/2` when
  `|γ i| ≤ T0`, `0 ≤ β ≤ 1`, and the functional equation symmetry, an injection `σ` with
  `|γ (σ i)| = |γ i|` and `β (σ i) = 1 - β i`. As in the paper, `x^β + x^(1-β) ≤ 1 + x`.
-/

namespace LeanLab.RamareSaouter2003.L3Zeros

open Real MeasureTheory Set
open LeanLab.RamareSaouter2003.Smooth LeanLab.RamareSaouter2003.Thm4JSplit

variable {ι : Type*}

/-- `log(t/2π)`. -/
noncomputable def ℓ (t : ℝ) : ℝ := Real.log (t / (2 * π))

/-- Main term of Lemma 1. -/
noncomputable def MN (t : ℝ) : ℝ := t / (2 * π) * ℓ t - t / (2 * π) + 7 / 8

/-- Error term of Lemma 1. -/
noncomputable def EN (t : ℝ) : ℝ := 0.67 * ℓ t

/-- **Lemma 1 of Ramaré-Saouter 2003, p. 14**, as counts of a zero family over finite sets,
both signs of the ordinate, for `10^3 ≤ T ≤ t`. CITED. -/
def Lemma1Count (γ : ι → ℝ) : Prop :=
  ∀ T t : ℝ, 1000 ≤ T → T ≤ t → ∀ s : Finset ι,
    ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤ 2 * ((MN t + EN t) - (MN T - EN T))

/-- The bound of Lemma 2, times `T^m`. -/
noncomputable def L2 (m : ℕ) (T : ℝ) : ℝ :=
  1 / (m * π) * (ℓ T + 1 / m) + 1.34 / T * (2 * ℓ T + 1)

/-- The zero sum of Lemma 3. -/
noncomputable def ZsF (γ β : ι → ℝ) (m : ℕ) (T x : ℝ) : ℝ :=
  ∑' i, if T < |γ i| then x ^ (β i) / |γ i| ^ (m + 1) else 0

/-! ### Numerics -/

lemma ℓ_pos {t : ℝ} (ht : 1000 ≤ t) : 0 < ℓ t := by
  unfold ℓ
  apply Real.log_pos
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d2]

lemma ℓ_mono {T t : ℝ} (hT : 1000 ≤ T) (ht : T ≤ t) : ℓ T ≤ ℓ t := by
  unfold ℓ
  apply Real.log_le_log (by positivity)
  gcongr

lemma MN_mono {T t : ℝ} (hT : 1000 ≤ T) (ht : T ≤ t) : MN T ≤ MN t := by
  have h1 := ℓ_pos hT
  have h2 := ℓ_mono hT ht
  have hl : 1 ≤ ℓ T := by
    unfold ℓ
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    have h1 := Real.exp_one_lt_d9
    have h2 := Real.pi_lt_d2
    have : Real.exp 1 * (2 * π) ≤ 2.72 * (2 * 3.15) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    linarith
  unfold MN
  have hp : 0 < 2 * π := by positivity
  have e : t / (2 * π) * ℓ t - t / (2 * π) - (T / (2 * π) * ℓ T - T / (2 * π)) =
      ((t - T) * (ℓ t - 1) + T * (ℓ t - ℓ T)) / (2 * π) := by field_simp; ring
  have : 0 ≤ ((t - T) * (ℓ t - 1) + T * (ℓ t - ℓ T)) / (2 * π) := by
    apply div_nonneg _ hp.le
    have : 0 ≤ (t - T) * (ℓ t - 1) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ T * (ℓ t - ℓ T) := mul_nonneg (by linarith) (by linarith)
    linarith
  linarith

/-! ### The layer cake for Lemma 2 -/

/-- The count majorant `H(t) = 2 ((M t + E t) - (M T - E T))`. -/
noncomputable def HC (T t : ℝ) : ℝ := 2 * ((MN t + EN t) - (MN T - EN T))

/-- The antiderivative of `(m+1) H(t)/t^(m+2)`. -/
noncomputable def FA (m : ℕ) (T x : ℝ) : ℝ :=
  -(HC T x / x ^ (m + 1) + 1 / (m * π) * (ℓ x + 1 / m) / x ^ m + 1.34 / (m + 1) / x ^ (m + 1))

lemma hasDerivAt_ℓ {x : ℝ} (hx : 0 < x) : HasDerivAt ℓ (1 / x) x := by
  have hp : (2 * π) ≠ 0 := by positivity
  have h := ((hasDerivAt_id' x).div_const (2 * π)).log (by positivity)
  convert h using 1
  · funext y; rfl
  · field_simp

lemma hasDerivAt_inv_pow (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => 1 / y ^ (n + 1)) (-(n + 1) / x ^ (n + 2)) x := by
  have h := (hasDerivAt_pow (n + 1) x).inv (pow_ne_zero _ hx.ne')
  convert h using 1
  · funext y; simp
  · simp only [Nat.add_sub_cancel]; push_cast; field_simp; ring

lemma hasDerivAt_FA (m : ℕ) (hm : 1 ≤ m) (T : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (FA m T) ((m + 1) * HC T x / x ^ (m + 2)) x := by
  have hl := hasDerivAt_ℓ hx
  have hp : 0 < π := Real.pi_pos
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  -- H' = ℓ/π + 1.34/x
  have hH : HasDerivAt (HC T) (ℓ x / π + 1.34 / x) x := by
    have hM : HasDerivAt MN (1 / (2 * π) * ℓ x + x / (2 * π) * (1 / x) - 1 / (2 * π)) x := by
      have := (((hasDerivAt_id' x).div_const (2 * π)).mul hl).sub ((hasDerivAt_id' x).div_const (2 * π))
      have := this.add_const (7 / 8)
      convert this using 1
      funext y; simp only [MN, Pi.mul_apply, Pi.sub_apply]
    have hE : HasDerivAt EN (0.67 * (1 / x)) x := hl.const_mul 0.67
    have := ((hM.add hE).sub_const (MN T - EN T)).const_mul 2
    convert this using 1
    · funext y; simp only [HC, Pi.add_apply]
    · field_simp; ring
  have hq1 := hasDerivAt_inv_pow m hx
  have hq0 : HasDerivAt (fun y : ℝ => 1 / y ^ m) (-(m : ℝ) / x ^ (m + 1)) x := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have := hasDerivAt_inv_pow k hx
    convert this using 1
    push_cast; ring
  have hA := (hH.mul hq1).add
    (((hl.add_const (1 / (m : ℝ))).const_mul (1 / (m * π))).mul hq0) |>.add
    (hq1.const_mul (1.34 / ((m : ℝ) + 1)))
  have hA' := hA.neg
  convert hA' using 1
  · funext y; simp only [FA, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]; ring
  · have hx1 : x ^ (m + 1) = x ^ m * x := pow_succ x m
    have hx2 : x ^ (m + 2) = x ^ m * x * x := by rw [pow_succ, pow_succ]
    rw [hx1, hx2]
    have hxm : 0 < x ^ m := pow_pos hx m
    field_simp
    ring

lemma FA_cont (m : ℕ) (T : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun x => (m + 1) * HC T x / x ^ (m + 2)) (Icc a b) := by
  have hc : ContinuousOn ℓ (Icc a b) := by
    unfold ℓ
    apply ContinuousOn.log (by fun_prop)
    intro x hx; have : 0 < x := by linarith [hx.1]
    positivity
  have hH : ContinuousOn (HC T) (Icc a b) := by
    unfold HC MN EN
    have : ContinuousOn (fun t : ℝ => t) (Icc a b) := continuousOn_id
    fun_prop
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx; have : 0 < x := by linarith [hx.1]
  positivity

/-- `∫_g^R (m+1)/t^(m+2) = 1/g^(m+1) - 1/R^(m+1)`. -/
lemma integral_phi (m : ℕ) {g R : ℝ} (hg : 0 < g) (hgR : g ≤ R) :
    ∫ t in Ioc g R, ((m : ℝ) + 1) / t ^ (m + 2) = 1 / g ^ (m + 1) - 1 / R ^ (m + 1) := by
  rw [← intervalIntegral.integral_of_le hgR]
  have hd : ∀ x ∈ uIcc g R, HasDerivAt (fun y : ℝ => -(1 / y ^ (m + 1)))
      (((m : ℝ) + 1) / x ^ (m + 2)) x := by
    intro x hx
    rw [uIcc_of_le hgR] at hx
    have := (hasDerivAt_inv_pow m (by linarith [hx.1] : 0 < x)).neg
    convert this using 1; ring
  have hc : ContinuousOn (fun x : ℝ => ((m : ℝ) + 1) / x ^ (m + 2)) (uIcc g R) := by
    rw [uIcc_of_le hgR]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; have : 0 < x := by linarith [hx.1]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  ring

/-- **Lemma 2 of Ramaré-Saouter 2003, p. 14**, upper half, over any finite set of zeros.
PROVED CONDITIONAL ON `Lemma1Count`. -/
theorem lemma2_upper {γ : ι → ℝ} (hN : Lemma1Count γ) {m : ℕ} (hm : 1 ≤ m) {T : ℝ}
    (hT : 1000 ≤ T) (s : Finset ι) :
    (∑ i ∈ s.filter (fun i => T < |γ i|), 1 / |γ i| ^ (m + 1)) ≤ L2 m T / T ^ m := by
  have hT0 : 0 < T := by linarith
  set S := s.filter (fun i => T < |γ i|) with hS
  set R : ℝ := T + ∑ i ∈ S, |γ i| with hR
  have hRT : T ≤ R := by
    have : 0 ≤ ∑ i ∈ S, |γ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hgR : ∀ i ∈ S, |γ i| ≤ R := by
    intro i hi
    have := Finset.single_le_sum (f := fun i => |γ i|) (fun j _ => abs_nonneg _) hi
    linarith
  have hR0 : 0 < R := by linarith
  set φ : ℝ → ℝ := fun t => ((m : ℝ) + 1) / t ^ (m + 2) with hφ
  have hφint : IntegrableOn φ (Ioc T R) := by
    rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; have : 0 < x := by linarith [hx.1]
    positivity
  -- each term as an integral
  have hterm : ∀ i ∈ S, 1 / |γ i| ^ (m + 1) =
      (∫ t in Ioc T R, (Ioi |γ i|).indicator φ t) + 1 / R ^ (m + 1) := by
    intro i hi
    have hgi : T < |γ i| := (Finset.mem_filter.mp hi).2
    rw [setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi, max_eq_right hgi.le,
      integral_phi m (by linarith) (hgR i hi)]
    ring
  have hint : ∀ i ∈ S, Integrable (fun t => (Ioi |γ i|).indicator φ t)
      (volume.restrict (Ioc T R)) := fun i _ => hφint.indicator measurableSet_Ioi
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← integral_finsetSum S hint,
    Finset.sum_const, nsmul_eq_mul]
  -- the majorant
  set g : ℝ → ℝ := fun x => (m + 1) * HC T x / x ^ (m + 2) with hg
  have hgint : IntegrableOn g (Ioc T R) := by
    rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (FA_cont m T hT0 hRT).integrableOn_Icc
  have hmono : ∫ t in Ioc T R, ∑ i ∈ S, (Ioi |γ i|).indicator φ t ≤ ∫ t in Ioc T R, g t := by
    refine setIntegral_mono_on (integrable_finsetSum S hint) hgint measurableSet_Ioc
      fun t ht => ?_
    have ht' : T < t := ht.1
    have ht0 : 0 < t := by linarith
    have hφ0 : 0 ≤ φ t := by simp only [hφ]; positivity
    have e : ∑ i ∈ S, (Ioi |γ i|).indicator φ t = ((S.filter (fun i => |γ i| < t)).card : ℝ) * φ t := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : |γ i| < t
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    rw [e]
    have hsub : S.filter (fun i => |γ i| < t) ⊆ s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t) := by
      intro i hi
      simp only [S, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, hi.1.2, hi.2.le⟩
    have hc1 : ((S.filter (fun i => |γ i| < t)).card : ℝ) ≤
        ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hc2 := hN T t hT ht'.le s
    have : g t = HC T t * φ t := by simp only [hg, hφ, HC]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (hc1.trans hc2) hφ0
  have hFTC : ∫ t in Ioc T R, g t = FA m T R - FA m T T := by
    rw [← intervalIntegral.integral_of_le hRT]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hRT] at hx
      exact hasDerivAt_FA m hm T (by linarith [hx.1])
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hRT]
      exact FA_cont m T hT0 hRT
  have hcard : (S.card : ℝ) ≤ HC T R := by
    have hsub : S ⊆ s.filter (fun i => T < |γ i| ∧ |γ i| ≤ R) := by
      intro i hi
      simp only [S, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, hi.2, hgR i (by simp [S, hi.1, hi.2])⟩
    have := hN T R hT hRT s
    have h1 : (S.card : ℝ) ≤ ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ R)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    unfold HC; linarith
  have hRm : 0 < R ^ (m + 1) := pow_pos hR0 _
  have hcard' : (S.card : ℝ) * (1 / R ^ (m + 1)) ≤ HC T R / R ^ (m + 1) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right hcard hRm.le
  -- the value at R is harmless
  have hlR := ℓ_pos (hT.trans hRT)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hFR : FA m T R + HC T R / R ^ (m + 1) ≤ 0 := by
    unfold FA
    have : 0 ≤ 1 / (m * π) * (ℓ R + 1 / m) / R ^ m := by positivity
    have : 0 ≤ 1.34 / ((m : ℝ) + 1) / R ^ (m + 1) := by positivity
    linarith
  -- the value at T
  have hlT := ℓ_pos hT
  have hHT : HC T T = 2.68 * ℓ T := by unfold HC EN; ring
  have hFT : -FA m T T ≤ L2 m T / T ^ m := by
    unfold FA L2
    rw [hHT]
    have hTm : 0 < T ^ m := pow_pos hT0 m
    have e1 : T ^ (m + 1) = T ^ m * T := pow_succ T m
    rw [e1]
    have h134 : 1.34 / ((m : ℝ) + 1) ≤ 1.34 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have key : 2.68 * ℓ T / (T ^ m * T) + 1.34 / ((m : ℝ) + 1) / (T ^ m * T) ≤
        1.34 / T * (2 * ℓ T + 1) / T ^ m := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : 2.68 * ℓ T + 1.34 / ((m : ℝ) + 1) ≤ 2.68 * ℓ T + 1.34 := by linarith
      have e : 1.34 / T * (2 * ℓ T + 1) * (T ^ m * T) = (2.68 * ℓ T + 1.34) * T ^ m := by
        field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h3 hTm.le
    rw [add_div]
    linarith
  linarith

/-! ### Lemma 3 -/

lemma rpow_add_rpow_le {x b : ℝ} (hx : 1 ≤ x) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    x ^ b + x ^ (1 - b) ≤ 1 + x := by
  have h1 : 1 ≤ x ^ b := Real.one_le_rpow hx hb0
  have h2 : 1 ≤ x ^ (1 - b) := Real.one_le_rpow hx (by linarith)
  have h3 : x ^ b * x ^ (1 - b) = x := by
    rw [← Real.rpow_add (by linarith)]; simp
  nlinarith

/-- `d_T i = 1/|γ i|^(m+1)` for `|γ i| > T`, else 0. -/
noncomputable def dT (γ : ι → ℝ) (m : ℕ) (T : ℝ) (i : ι) : ℝ :=
  if T < |γ i| then 1 / |γ i| ^ (m + 1) else 0

lemma sum_dT (γ : ι → ℝ) (m : ℕ) (T : ℝ) (s : Finset ι) :
    ∑ i ∈ s, dT γ m T i = ∑ i ∈ s.filter (fun i => T < |γ i|), 1 / |γ i| ^ (m + 1) := by
  rw [Finset.sum_filter]; rfl

lemma dT_nonneg (γ : ι → ℝ) (m : ℕ) (T : ℝ) (i : ι) : 0 ≤ dT γ m T i := by
  unfold dT; split_ifs <;> positivity

/-- **Lemma 3 of Ramaré-Saouter 2003, p. 15**, for a zero family. PROVED CONDITIONAL ON
`Lemma1Count γ`, RH to height `T0` for the family, `0 ≤ β ≤ 1` and the functional equation
symmetry `σ`. -/
theorem lemma3_of {γ β : ι → ℝ} {T0 : ℝ} (hN : Lemma1Count γ) (σ : ι → ι)
    (hσ : Function.Injective σ) (hσγ : ∀ i, |γ (σ i)| = |γ i|) (hσβ : ∀ i, β (σ i) = 1 - β i)
    (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ 1) (hRH : ∀ i, |γ i| ≤ T0 → β i = 1 / 2) :
    Lemma3Bound (ZsF γ β) T0 := by
  intro m T x hm hT hTT0 hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 1000 ≤ T0 := hT.trans hTT0
  set a : ι → ℝ := fun i => if T < |γ i| then x ^ (β i) / |γ i| ^ (m + 1) else 0 with ha
  set b : ι → ℝ := fun i => if T < |γ i| then x ^ (1 - β i) / |γ i| ^ (m + 1) else 0 with hb
  have ha0 : ∀ i, 0 ≤ a i := fun i => by simp only [ha]; split_ifs <;> positivity
  have hb0 : ∀ i, 0 ≤ b i := fun i => by simp only [hb]; split_ifs <;> positivity
  have hL2T := lemma2_upper hN hm hT
  have hab_le : ∀ i, a i ≤ x * dT γ m T i ∧ b i ≤ x * dT γ m T i := by
    intro i
    simp only [ha, hb, dT]
    split_ifs with h
    · have e1 : x ^ (β i) ≤ x := by
        calc x ^ (β i) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (hβ i).2
          _ = x := Real.rpow_one x
      have e2 : x ^ (1 - β i) ≤ x := by
        calc x ^ (1 - β i) ≤ x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [(hβ i).1])
          _ = x := Real.rpow_one x
      have hg : 0 < |γ i| ^ (m + 1) := pow_pos (by linarith) _
      rw [mul_one_div]
      exact ⟨div_le_div_of_nonneg_right e1 hg.le, div_le_div_of_nonneg_right e2 hg.le⟩
    · simp
  have hsumx : ∀ s : Finset ι, ∑ i ∈ s, x * dT γ m T i ≤ x * (L2 m T / T ^ m) := by
    intro s
    rw [← Finset.mul_sum, sum_dT]
    exact mul_le_mul_of_nonneg_left (hL2T s) hx0.le
  have hsa : Summable a := summable_of_sum_le (fun i => ha0 i)
    fun s => (Finset.sum_le_sum fun i _ => (hab_le i).1).trans (hsumx s)
  have hsb : Summable b := summable_of_sum_le (fun i => hb0 i)
    fun s => (Finset.sum_le_sum fun i _ => (hab_le i).2).trans (hsumx s)
  have hab : a = b ∘ σ := by
    funext i
    simp only [ha, hb, Function.comp, hσγ, hσβ]
    congr 2; ring_nf
  have hle : ∑' i, a i ≤ ∑' i, b i := by
    rw [hab]; exact tsum_comp_le_tsum_of_inj hsb hb0 hσ
  have hhalf : ∑' i, a i ≤ ∑' i, (a i + b i) / 2 := by
    rw [tsum_div_const, hsa.tsum_add hsb]; linarith
  set K : ℝ := 1 + 1 / 10 ^ 5
  have hpt : ∀ i, (a i + b i) / 2 ≤ √x * dT γ m T i + K * x / 2 * dT γ m T0 i := by
    intro i
    simp only [ha, hb, dT]
    by_cases h : T < |γ i|
    · have hg : 0 < |γ i| ^ (m + 1) := pow_pos (by linarith) _
      rw [if_pos h, if_pos h, if_pos h]
      by_cases h0 : T0 < |γ i|
      · rw [if_pos h0]
        have hs := rpow_add_rpow_le hx1 (hβ i).1 (hβ i).2
        have hK : 1 + x ≤ K * x := by simp only [K]; nlinarith
        have hsq : 0 ≤ √x := Real.sqrt_nonneg x
        have : (x ^ (β i) / |γ i| ^ (m + 1) + x ^ (1 - β i) / |γ i| ^ (m + 1)) / 2 ≤
            K * x / 2 * (1 / |γ i| ^ (m + 1)) := by
          rw [← add_div, div_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith
        have : 0 ≤ √x * (1 / |γ i| ^ (m + 1)) := by positivity
        linarith
      · rw [if_neg h0]
        have hb' := hRH i (le_of_not_gt h0)
        rw [hb']
        have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
        rw [e, ← Real.sqrt_eq_rpow]
        ring_nf; rfl
    · rw [if_neg h, if_neg h, if_neg h]
      have : ¬ T0 < |γ i| := fun h' => h (lt_of_le_of_lt hTT0 h')
      rw [if_neg this]; simp
  have hL2T0 := lemma2_upper hN hm hT0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hLsm : ∀ t : ℝ, 1000 ≤ t → L2 m t ≤ sm m t := by
    intro t ht
    have hl := ℓ_pos ht
    have h0 : 0 ≤ L2 m t := by unfold L2; positivity
    have : sm m t = L2 m t * (1 + 1 / 10 ^ 5) := by unfold sm L2 ℓ; ring
    rw [this]; nlinarith
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, (a i + b i) / 2 ≤
      sm m T * √x / T ^ m + sm m T0 * x / (2 * T0 ^ m) := by
    intro s
    refine (Finset.sum_le_sum fun i _ => hpt i).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_dT, sum_dT]
    have hTm : 0 < T ^ m := pow_pos (by linarith) m
    have hT0m : 0 < T0 ^ m := pow_pos (by linarith) m
    have h1 : √x * ∑ i ∈ s.filter (fun i => T < |γ i|), 1 / |γ i| ^ (m + 1) ≤
        sm m T * √x / T ^ m := by
      calc _ ≤ √x * (L2 m T / T ^ m) := mul_le_mul_of_nonneg_left (hL2T s) (Real.sqrt_nonneg x)
        _ ≤ √x * (sm m T / T ^ m) := by
          gcongr; exact hLsm T hT
        _ = _ := by ring
    have h2 : K * x / 2 * ∑ i ∈ s.filter (fun i => T0 < |γ i|), 1 / |γ i| ^ (m + 1) ≤
        sm m T0 * x / (2 * T0 ^ m) := by
      have hK0 : 0 ≤ K * x / 2 := by simp only [K]; positivity
      have hl := ℓ_pos hT0
      have hsmL : sm m T0 = L2 m T0 * K := by simp only [K]; unfold sm L2 ℓ; ring
      calc _ ≤ K * x / 2 * (L2 m T0 / T0 ^ m) := mul_le_mul_of_nonneg_left (hL2T0 s) hK0
        _ = _ := by rw [hsmL]; field_simp
    linarith
  have hRHS : 0 ≤ sm m T * √x / T ^ m + sm m T0 * x / (2 * T0 ^ m) := by
    have := hLsm T hT; have := hLsm T0 hT0
    have h1 : 0 ≤ L2 m T := by have := ℓ_pos hT; unfold L2; positivity
    have h2 : 0 ≤ L2 m T0 := by have := ℓ_pos hT0; unfold L2; positivity
    have : 0 ≤ sm m T := by linarith
    have : 0 ≤ sm m T0 := by linarith
    positivity
  refine ⟨tsum_nonneg ha0, ?_⟩
  exact hhalf.trans (tsum_le_of_sum_le' hRHS hfin)

/-- **Table 1 row one** with Lemma 3 discharged for a zero family. PROVED CONDITIONAL ON
`MVBrunTitchmarsh`, `SchoenfeldPT 0.998697 1.001093`, `JLower15` for the zero sum `ZsF γ β`,
`Lemma1Count γ`, RH to height `3.3e9` for the family, `0 ≤ β ≤ 1`, the symmetry `σ`, and
`Lemma1Upper NT`. -/
theorem theorem2At1e20_of_family (hMV : Thm4Parts.MVBrunTitchmarsh)
    (hS : Thm4Parts.SchoenfeldPT 0.998697 1.001093) {NT : ℝ → ℝ} {γ β : ι → ℝ}
    (h15 : JLower15 NT (ZsF γ β) 3300000000) (hN : Lemma1Count γ) (σ : ι → ι)
    (hσ : Function.Injective σ) (hσγ : ∀ i, |γ (σ i)| = |γ i|) (hσβ : ∀ i, β (σ i) = 1 - β i)
    (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ 1) (hRH : ∀ i, |γ i| ≤ 3300000000 → β i = 1 / 2)
    (hU : Row1.Lemma1Upper NT) : Theorem2At1e20 :=
  theorem2At1e20_of_split hMV hS h15 (lemma3_of hN σ hσ hσγ hσβ hβ hRH) hU

end LeanLab.RamareSaouter2003.L3Zeros

#print axioms LeanLab.RamareSaouter2003.L3Zeros.lemma2_upper
#print axioms LeanLab.RamareSaouter2003.L3Zeros.lemma3_of
#print axioms LeanLab.RamareSaouter2003.L3Zeros.theorem2At1e20_of_family
