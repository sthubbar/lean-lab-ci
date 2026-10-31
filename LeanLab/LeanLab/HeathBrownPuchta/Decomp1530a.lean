/-
Heath-Brown and Puchta 2002, Integers represented as a sum of primes and powers of two,
arXiv math/0201299. Unit U-1530, run 20261026T0004Z-24325, type DECOMPOSE, file a of three.

Lemma 1, Section 7: the measure of the exceptional set `𝒜_λ = {α : |T(α)| ≥ λL}` is
`≪ N^{-E(λ)}`. In Assembly.lean this enters as the field `lemma1_in` of `AnalyticInputs`, still an
open input. The Section 7 route, split here into leaves:

* `T_L(α) = Σ_{0 ≤ n < L} e(α 2^n)`, and `T_L(α) = T_h(α) + T_{L-h}(2^h α)`;
* the rotation step, display before (42): `|z| ≥ λL` gives some `ρ_m = e(-m/M)`,
  `M = 1 + [2π/ϖ]`, with `Re(ρ_m z) ≥ (1 - ϖ) λL`;
* the exponential Chebyshev step (42) with `S(ξ, ρ, L) = ∫₀¹ exp(ξ Re(ρ T_L(α))) dα`;
* the transfer step `S(ξ, ρ, L) ≤ S(ξ, ρ, L - h) F(ξ, h)`, F of display 43, and its iteration
  `S(ξ, ρ, L) ≪ F(ξ, h)^{L/h}`;
* the conversion `e^{-ξλL} F^{L/h} ≪ N^{-E}`, `E = ξλ/log 2 - log F/(h log 2)`.

Page numbers are not visible in the arXiv text read for this unit; Section and display numbers
are given instead. The paper copy was NOT FOUND in either lab location; the text used is arXiv
math/0201299 through WebFetch, 2026-10-26.

ASSEMBLY, real proofs with no sorry of their own, CONDITIONAL ON the leaves below:
`Sexp_bound`, `S(ξ, ρ, L) ≤ e^{ξh} F(ξ, h)^{[L/h]}`, and `exceptional_bound`, the measure of
`{α ∈ [0,1] : Re(ρ T_L(α)) ≥ t}` is at most `e^{-ξt} e^{ξh} F(ξ, h)^{[L/h]}`.

AI-written Lean code, Claude, 2026-10-26. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib

namespace LeanLab.HeathBrownPuchta.Decomp1530a

open Finset Real MeasureTheory intervalIntegral

/-- `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `T_L(α) = Σ_{0 ≤ n < L} e(α 2^n)`, Section 7. -/
noncomputable def TL (L : ℕ) (α : ℝ) : ℂ := ∑ n ∈ range L, ee (α * 2 ^ n)

/-- `S(ξ, ρ, L) = ∫₀¹ exp(ξ Re(ρ T_L(α))) dα`, Section 7, before (42). -/
noncomputable def Sexp (ξ : ℝ) (ρ : ℂ) (L : ℕ) : ℝ :=
  ∫ α in (0 : ℝ)..1, Real.exp (ξ * (ρ * TL L α).re)

/-- The inner average of display 43:
`2^{-h} Σ_{0 ≤ r < 2^h} exp(ξ Re(ρ T_h((β + r)/2^h)))`. -/
noncomputable def avg (ξ : ℝ) (ρ : ℂ) (h : ℕ) (β : ℝ) : ℝ :=
  (1 / 2 ^ h) * ∑ r ∈ range (2 ^ h), Real.exp (ξ * (ρ * TL h ((β + r) / 2 ^ h)).re)

/-- `F(ξ, h)`, display 43: the supremum of `avg` over `β ∈ [0,1]` and `|ρ| = 1`. -/
noncomputable def F (ξ : ℝ) (h : ℕ) : ℝ :=
  ⨆ p : {p : ℝ × ℂ // p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ‖p.2‖ = 1}, avg ξ p.1.2 h p.1.1

theorem avg_nonneg (ξ : ℝ) (ρ : ℂ) (h : ℕ) (β : ℝ) : 0 ≤ avg ξ ρ h β := by
  unfold avg
  have : (0 : ℝ) ≤ ∑ r ∈ range (2 ^ h), Real.exp (ξ * (ρ * TL h ((β + r) / 2 ^ h)).re) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  positivity

/-! ### Leaves on `T_L` -/

/-- LEAF. Unit U-1530. The additive character has period one: `e(x + n) = e(x)` for every
integer `n`; Section 7, used for the period one property of `T_L`. -/
theorem ee_int_shift (x : ℝ) (n : ℤ) : ee (x + n) = ee x := by
  unfold ee
  push_cast
  rw [mul_add, Complex.exp_add]
  have hn := Complex.exp_int_mul_two_pi_mul_I n
  rw [mul_comm (2 * (π : ℂ) * Complex.I) (n : ℂ), hn, mul_one]

/-- LEAF. Unit U-1530. For `h ≤ L`, `T_L(α) = T_h(α) + T_{L-h}(2^h α)`; Section 7, the identity
before display 43. -/
theorem TL_split (L h : ℕ) (hh : h ≤ L) (α : ℝ) :
    TL L α = TL h α + TL (L - h) (2 ^ h * α) := by
  unfold TL
  conv_lhs => rw [show L = h + (L - h) by omega, sum_range_add]
  congr 1
  apply sum_congr rfl
  intro n hn
  congr 1
  rw [pow_add]
  ring

/-- LEAF. Unit U-1530. `T_L` has period one: `T_L(α + 1) = T_L(α)`; Section 7, the period one
property used in the transfer step. -/
theorem TL_periodic (L : ℕ) (α : ℝ) : TL L (α + 1) = TL L α := by
  unfold TL
  apply sum_congr rfl
  intro n hn
  rw [add_mul, one_mul]
  simpa only [Int.cast_pow, Int.cast_ofNat] using ee_int_shift (α * 2 ^ n) ((2 : ℤ) ^ n)

/-- LEAF. Unit U-1530. The trivial bound `|T_L(α)| ≤ L`; Section 7. -/
theorem TL_norm_le (L : ℕ) (α : ℝ) : ‖TL L α‖ ≤ L := by
  unfold TL
  calc
    ‖∑ n ∈ range L, ee (α * 2 ^ n)‖ ≤ ∑ n ∈ range L, ‖ee (α * 2 ^ n)‖ := norm_sum_le _ _
    _ = L := by simp [ee, Complex.norm_exp, -Complex.ofReal_pow]

/-- LEAF. Unit U-1530. `α ↦ Re(ρ T_L(α))` is continuous; Section 7, needed so that the integrals
in (42) exist. -/
theorem TL_re_continuous (L : ℕ) (ρ : ℂ) : Continuous fun α : ℝ => (ρ * TL L α).re := by
  unfold TL ee
  fun_prop

/-- The pointwise bound used on paper pages 29 and 30 before display 43. -/
theorem exp_pointwise_le (ξ : ℝ) {ρ : ℂ} (hρ : ‖ρ‖ = 1) (j : ℕ) (α : ℝ) :
    Real.exp (ξ * (ρ * TL j α).re) ≤ Real.exp (|ξ| * j) := by
  apply Real.exp_le_exp.mpr
  calc
    ξ * (ρ * TL j α).re ≤ |ξ * (ρ * TL j α).re| := le_abs_self _
    _ = |ξ| * |(ρ * TL j α).re| := abs_mul _ _
    _ ≤ |ξ| * ‖ρ * TL j α‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
    _ = |ξ| * ‖TL j α‖ := by rw [norm_mul, hρ, one_mul]
    _ ≤ |ξ| * j := mul_le_mul_of_nonneg_left (TL_norm_le j α) (abs_nonneg _)

/-! ### Leaves on the averages and on `F` -/

/-- LEAF. Unit U-1530. Each inner average of display 43 with `β ∈ [0,1]` and `|ρ| = 1` is at
most `F(ξ, h)`; this needs the family to be bounded above, which holds since each term is at most
`exp(|ξ| h)`. Section 7, display 43. -/
theorem avg_le_F (ξ : ℝ) (h : ℕ) {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) {ρ : ℂ} (hρ : ‖ρ‖ = 1) :
    avg ξ ρ h β ≤ F ξ h := by
  have bound : ∀ (ρ : ℂ), ‖ρ‖ = 1 → ∀ β : ℝ, avg ξ ρ h β ≤ Real.exp (|ξ| * h) := by
    intro ρ hρ β
    unfold avg
    calc
      _ ≤ (1 / 2 ^ h) * ∑ r ∈ range (2 ^ h), Real.exp (|ξ| * h) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun r _ => exp_pointwise_le ξ hρ h _) (by positivity)
      _ = Real.exp (|ξ| * h) := by
        simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
  apply le_ciSup (f := fun p : {p : ℝ × ℂ // p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ‖p.2‖ = 1} =>
      avg ξ p.1.2 h p.1.1) ?_ ⟨(β, ρ), hβ, hρ⟩
  exact ⟨Real.exp (|ξ| * h), fun y ⟨p, hp⟩ => hp ▸ bound p.1.2 p.2.2 p.1.1⟩

/-- LEAF. Unit U-1530. For a continuous function of period one,
`∫₀¹ f = ∫₀¹ 2^{-h} Σ_{0 ≤ r < 2^h} f((β + r)/2^h) dβ`; Section 7, the averaging identity
before display 43. -/
theorem periodic_average (f : ℝ → ℝ) (hf : Continuous f) (hper : ∀ x, f (x + 1) = f x)
    (h : ℕ) :
    ∫ α in (0 : ℝ)..1, f α =
      ∫ β in (0 : ℝ)..1, (1 / 2 ^ h) * ∑ r ∈ range (2 ^ h), f ((β + r) / 2 ^ h) := by
  have hd : (2 : ℝ) ^ h ≠ 0 := by positivity
  have hi (r : ℕ) : IntervalIntegrable (fun β : ℝ => f ((β + r) / 2 ^ h)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact hf.comp (by fun_prop)
  have single (r : ℕ) :
      (∫ β in (0 : ℝ)..1, f ((β + r) / 2 ^ h)) =
        2 ^ h * ∫ β in (r : ℝ) / 2 ^ h..((r : ℝ) + 1) / 2 ^ h, f β := by
    have hh := integral_comp_div_add (a := (0 : ℝ)) (b := 1) f hd ((r : ℝ) / 2 ^ h)
    simp only [zero_div, zero_add, smul_eq_mul] at hh
    simpa only [add_div, add_comm] using hh
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun r _ => hi r)]
  simp_rw [single]
  rw [← mul_sum, ← mul_assoc, one_div_mul_cancel hd, one_mul]
  have hh := sum_integral_adjacent_intervals (a := fun r : ℕ => (r : ℝ) / 2 ^ h)
    (n := 2 ^ h) (μ := volume) (fun r hr => hf.intervalIntegrable _ _)
  simpa only [Nat.cast_zero, zero_div, Nat.cast_pow, Nat.cast_ofNat, div_self hd,
    Nat.cast_add, Nat.cast_one] using hh.symm

/-- LEAF. Unit U-1530. The transfer step: for `h ≤ L`, `ξ ≥ 0` and `|ρ| = 1`,
`S(ξ, ρ, L) ≤ S(ξ, ρ, L - h) F(ξ, h)`; Section 7, the inequality before display 43, from
`TL_split`, `TL_periodic`, `periodic_average` and `avg_le_F`. -/
theorem transfer (ξ : ℝ) (hξ : 0 ≤ ξ) {ρ : ℂ} (hρ : ‖ρ‖ = 1) {L h : ℕ} (hh : h ≤ L) :
    Sexp ξ ρ L ≤ Sexp ξ ρ (L - h) * F ξ h := by
  have hd : (2 : ℝ) ^ h ≠ 0 := by positivity
  have hs (β : ℝ) (r : ℕ) : TL L ((β + r) / 2 ^ h) =
      TL h ((β + r) / 2 ^ h) + TL (L - h) β := by
    rw [TL_split L h hh]
    congr 1
    rw [mul_div_cancel₀ _ hd]
    simpa using ((show Function.Periodic (TL (L - h)) 1 from TL_periodic (L - h)).nat_mul r β)
  have hc : Continuous (fun α : ℝ => Real.exp (ξ * (ρ * TL L α).re)) :=
    Real.continuous_exp.comp (continuous_const.mul (TL_re_continuous L ρ))
  have hm : Continuous (fun α : ℝ => Real.exp (ξ * (ρ * TL (L - h) α).re)) :=
    Real.continuous_exp.comp (continuous_const.mul (TL_re_continuous (L - h) ρ))
  have ha : Continuous (avg ξ ρ h) := by unfold avg TL ee; fun_prop
  have heq (β : ℝ) :
      (1 / 2 ^ h) * ∑ r ∈ range (2 ^ h), Real.exp (ξ * (ρ * TL L ((β + r) / 2 ^ h)).re) =
        Real.exp (ξ * (ρ * TL (L - h) β).re) * avg ξ ρ h β := by
    simp_rw [hs, mul_add, Complex.add_re, mul_add, Real.exp_add]
    unfold avg
    rw [← sum_mul]
    ring
  calc
    Sexp ξ ρ L = ∫ β in (0 : ℝ)..1,
        (1 / 2 ^ h) * ∑ r ∈ range (2 ^ h), Real.exp (ξ * (ρ * TL L ((β + r) / 2 ^ h)).re) :=
      periodic_average _ hc (fun α => by rw [TL_periodic]) h
    _ = ∫ β in (0 : ℝ)..1, Real.exp (ξ * (ρ * TL (L - h) β).re) * avg ξ ρ h β := by
      apply intervalIntegral.integral_congr
      intro β hβ
      exact heq β
    _ ≤ ∫ β in (0 : ℝ)..1, Real.exp (ξ * (ρ * TL (L - h) β).re) * F ξ h :=
      intervalIntegral.integral_mono_on zero_le_one ((hm.mul ha).intervalIntegrable 0 1)
        ((hm.mul continuous_const).intervalIntegrable 0 1) (fun β hβ =>
          mul_le_mul_of_nonneg_left (avg_le_F ξ h hβ hρ) (Real.exp_pos _).le)
    _ = Sexp ξ ρ (L - h) * F ξ h := intervalIntegral.integral_mul_const _ _

/-- LEAF. Unit U-1530. For `|ρ| = 1`, `S(ξ, ρ, j) ≤ exp(|ξ| j)`, from `|T_j| ≤ j`; Section 7,
the start of the iteration. -/
theorem Sexp_le_small (ξ : ℝ) {ρ : ℂ} (hρ : ‖ρ‖ = 1) (j : ℕ) :
    Sexp ξ ρ j ≤ Real.exp (|ξ| * j) := by
  unfold Sexp
  have hc : Continuous fun α : ℝ => Real.exp (ξ * (ρ * TL j α).re) :=
    Real.continuous_exp.comp (continuous_const.mul (TL_re_continuous j ρ))
  calc
    _ ≤ ∫ _α in (0 : ℝ)..1, Real.exp (|ξ| * j) :=
      intervalIntegral.integral_mono_on zero_le_one (hc.intervalIntegrable 0 1)
        intervalIntegrable_const (fun α _ => exp_pointwise_le ξ hρ j α)
    _ = Real.exp (|ξ| * j) := by simp

/-- LEAF. Unit U-1530. Iterating a one step bound: if `F₀ ≥ 0`, `h ≥ 1` and
`s(L) ≤ s(L - h) F₀` whenever `h ≤ L`, then `s(L) ≤ s(L mod h) F₀^{[L/h]}` for every `L`;
Section 7, the iteration with `n = [L/h]`. -/
theorem iterate_bound (s : ℕ → ℝ) {F0 : ℝ} (hF0 : 0 ≤ F0) {h : ℕ} (hh : 0 < h)
    (step : ∀ L, h ≤ L → s L ≤ s (L - h) * F0) (L : ℕ) :
    s L ≤ s (L % h) * F0 ^ (L / h) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
    by_cases hL : h ≤ L
    · have hsub : L - h < L := by omega
      have hdiv : L / h = (L - h) / h + 1 := by
        conv_lhs => rw [← Nat.sub_add_cancel hL]
        rw [Nat.add_div_right _ hh]
      have hmod : (L - h) % h = L % h := by
        conv_rhs => rw [← Nat.sub_add_cancel hL]
        rw [Nat.add_mod_right]
      calc
        s L ≤ s (L - h) * F0 := step L hL
        _ ≤ (s ((L - h) % h) * F0 ^ ((L - h) / h)) * F0 :=
          mul_le_mul_of_nonneg_right (ih (L - h) hsub) hF0
        _ = s (L % h) * F0 ^ (L / h) := by rw [hmod, hdiv, pow_succ]; ring
    · rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), pow_zero, mul_one]

/-! ### Leaves for display 42 and the exponent -/

/-- LEAF. Unit U-1530. The exponential Chebyshev step: for continuous `g` and `ξ ≥ 0`,
`meas{α ∈ [0,1] : g(α) ≥ t} · e^{ξt} ≤ ∫₀¹ e^{ξ g(α)} dα`; Section 7, display 42. -/
theorem exp_markov (g : ℝ → ℝ) (hg : Continuous g) {ξ : ℝ} (hξ : 0 ≤ ξ) (t : ℝ) :
    (volume {α ∈ Set.Icc (0 : ℝ) 1 | t ≤ g α}).toReal * Real.exp (ξ * t) ≤
      ∫ α in (0 : ℝ)..1, Real.exp (ξ * g α) := by
  let f : ℝ → ℝ := fun α => Real.exp (ξ * g α)
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul hg)
  have hi : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hh := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (Filter.Eventually.of_forall fun α => (Real.exp_pos (ξ * g α)).le) hi (Real.exp (ξ * t))
  have hsub : {α ∈ Set.Icc (0 : ℝ) 1 | t ≤ g α} ⊆
      {α ∈ Set.Icc (0 : ℝ) 1 | Real.exp (ξ * t) ≤ f α} := by
    intro α hα
    exact ⟨hα.1, Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hα.2 hξ)⟩
  have hmeas := measure_mono (μ := volume) hsub
  have hfset : MeasurableSet {α : ℝ | Real.exp (ξ * t) ≤ f α} :=
    measurableSet_le measurable_const hf.measurable
  rw [measureReal_def, Measure.restrict_apply hfset] at hh
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have hm : (volume {α ∈ Set.Icc (0 : ℝ) 1 | t ≤ g α}).toReal ≤
      (volume {α ∈ Set.Icc (0 : ℝ) 1 | Real.exp (ξ * t) ≤ f α}).toReal := by
    apply ENNReal.toReal_mono _ hmeas
    exact ne_of_lt (lt_of_le_of_lt (measure_mono fun _ h => h.1) (by simp))
  have he := mul_le_mul_of_nonneg_right hm (Real.exp_pos (ξ * t)).le
  have heq : {α : ℝ | Real.exp (ξ * t) ≤ f α} ∩ Set.Icc 0 1 =
      {α ∈ Set.Icc (0 : ℝ) 1 | Real.exp (ξ * t) ≤ f α} := by ext α; simp [and_comm]
  rw [heq] at hh
  exact he.trans (by simpa [mul_comm] using hh)

/-- LEAF. Unit U-1530. The rotation step: with `M = 1 + [2π/ϖ]` and `0 < ϖ ≤ 1`, every complex
`z` with `|z| ≥ r ≥ 0` has some `m < M` with `Re(e(-m/M) z) ≥ (1 - ϖ) r`; Section 7, the
display before (42). -/
theorem rotation {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) {r : ℝ} (hr : 0 ≤ r) {z : ℂ}
    (hz : r ≤ ‖z‖) :
    ∃ m < 1 + ⌊2 * π / ϖ⌋₊,
      (1 - ϖ) * r ≤ (ee (-((m : ℝ) / ((1 + ⌊2 * π / ϖ⌋₊ : ℕ) : ℝ))) * z).re := by
  let M : ℕ := 1 + ⌊2 * π / ϖ⌋₊
  have hM : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : 0 < 2 * π := Real.two_pi_pos
  let θ : ℝ := toIcoMod hp 0 z.arg
  have hθ : 0 ≤ θ ∧ θ < 2 * π := toIcoMod_mem_Ico' hp z.arg
  obtain ⟨k, hk⟩ := ((toIcoMod_eq_iff hp).mp (rfl : toIcoMod hp 0 z.arg = θ)).2
  have hpolar : (‖z‖ : ℂ) * Complex.exp (Complex.I * θ) = z := by
    have he : Complex.exp (Complex.I * (z.arg : ℂ)) = Complex.exp (Complex.I * θ) := by
      rw [hk]
      push_cast
      simp only [zsmul_eq_mul]
      rw [mul_add, Complex.exp_add]
      have hh := Complex.exp_int_mul_two_pi_mul_I k
      have hmul : Complex.I * ((k : ℂ) * (2 * (π : ℂ))) = k * (2 * π * Complex.I) := by ring
      rw [hmul, hh, mul_one]
    rw [← he, mul_comm Complex.I]
    exact Complex.norm_mul_exp_arg_mul_I z
  let m : ℕ := ⌊(M : ℝ) * θ / (2 * π)⌋₊
  have hx : 0 ≤ (M : ℝ) * θ / (2 * π) := div_nonneg (mul_nonneg hMr.le hθ.1) hp.le
  have hm : m < M := by
    apply (Nat.floor_lt hx).mpr
    rw [div_lt_iff₀ hp]
    nlinarith
  have hfloor : (m : ℝ) ≤ (M : ℝ) * θ / (2 * π) := Nat.floor_le hx
  have hfloor' : (M : ℝ) * θ / (2 * π) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hδ0 : 0 ≤ θ - 2 * π * m / M := by
    rw [le_div_iff₀ hp] at hfloor
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hMr]
    nlinarith
  have hδ : θ - 2 * π * m / M ≤ ϖ := by
    have hbound := Nat.lt_floor_add_one (2 * π / ϖ)
    have hMbound : 2 * π / ϖ < (M : ℝ) := by dsimp [M]; push_cast; linarith
    have hMprod : 2 * π < (M : ℝ) * ϖ := (div_lt_iff₀ hϖ0).mp hMbound
    rw [div_lt_iff₀ hp] at hfloor'
    apply (le_of_lt ?_)
    have heq : (θ - 2 * π * m / M) * M = θ * M - 2 * π * m := by field_simp
    nlinarith
  have hn := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ - 2 * π * m / M)
  rw [Real.norm_eq_abs, abs_of_nonneg hδ0] at hn
  have hre : 1 - ϖ ≤ (Complex.exp (Complex.I * ((θ - 2 * π * m / M : ℝ) : ℂ))).re := by
    have habs := Complex.abs_re_le_norm (Complex.exp (Complex.I * ((θ - 2 * π * m / M : ℝ) : ℂ)) - 1)
    simp only [Complex.sub_re, Complex.one_re] at habs
    have hneg := neg_le_abs ((Complex.exp (Complex.I * ((θ - 2 * π * m / M : ℝ) : ℂ))).re - 1)
    linarith
  refine ⟨m, hm, ?_⟩
  have heq : ee (-((m : ℝ) / (M : ℝ))) * z =
      (‖z‖ : ℂ) * Complex.exp (Complex.I * ((θ - 2 * π * m / M : ℝ) : ℂ)) := by
    conv_lhs => rw [← hpolar]
    unfold ee
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  change (1 - ϖ) * r ≤ (ee (-((m : ℝ) / (M : ℝ))) * z).re
  rw [heq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith [mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hϖ1),
    mul_le_mul_of_nonneg_left hre (norm_nonneg z)]

/-- LEAF. Unit U-1530. The exponent conversion: if `c ≥ 0`, `F₀ ≥ 1`, `h ≥ 1`, `N ≥ 1` and
`log N/log 2 - A ≤ L ≤ log N/log 2`, then
`e^{-cL} F₀^{[L/h]} ≤ e^{cA} N^{-(c/log 2 - log F₀/(h log 2))}`; Section 7, the step from (42)
and the iteration to `E(λ) = ξλ/log 2 - log F/(h log 2)`, with `c = ξ(1 - ϖ)λ`. -/
theorem exponent_conversion {c F0 A N : ℝ} (hc : 0 ≤ c) (hF0 : 1 ≤ F0) {h L : ℕ} (hh : 0 < h)
    (hN : 1 ≤ N) (hL1 : Real.log N / Real.log 2 - A ≤ L) (hL2 : (L : ℝ) ≤ Real.log N / Real.log 2) :
    Real.exp (-(c * L)) * F0 ^ (L / h) ≤
      Real.exp (c * A) * N ^ (-(c / Real.log 2 - Real.log F0 / (h * Real.log 2))) := by
  have hNp : 0 < N := by linarith
  have hFp : 0 < F0 := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhp : (0 : ℝ) < h := by exact_mod_cast hh
  have hlogF : 0 ≤ Real.log F0 := Real.log_nonneg hF0
  have hdiv : ((L / h : ℕ) : ℝ) ≤ Real.log N / (h * Real.log 2) := by
    calc
      _ ≤ (L : ℝ) / h := Nat.cast_div_le
      _ ≤ (Real.log N / Real.log 2) / h := div_le_div_of_nonneg_right hL2 hhp.le
      _ = _ := by ring
  rw [← Real.rpow_natCast F0 (L / h), Real.rpow_def_of_pos hFp,
    Real.rpow_def_of_pos hNp, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he1 := mul_le_mul_of_nonneg_left hL1 hc
  have he2 := mul_le_mul_of_nonneg_left hdiv hlogF
  have heq : c * A + Real.log N * -(c / Real.log 2 - Real.log F0 / (h * Real.log 2)) =
      -(c * (Real.log N / Real.log 2 - A)) + Real.log F0 * (Real.log N / (h * Real.log 2)) := by ring
  rw [heq]
  nlinarith

/-! ### Assemblies -/

/-- ASSEMBLY, CONDITIONAL ON the leaves `transfer`, `iterate_bound`, `Sexp_le_small` and
`avg_le_F`: for `h ≥ 1`, `ξ ≥ 0`, `|ρ| = 1`, `S(ξ, ρ, L) ≤ e^{ξh} F(ξ, h)^{[L/h]}`, Section 7,
the bound `S(ξ, ρ, L) ≪ F(ξ, h)^{L/h}`. -/
theorem Sexp_bound {ξ : ℝ} (hξ : 0 ≤ ξ) {ρ : ℂ} (hρ : ‖ρ‖ = 1) {h : ℕ} (hh : 0 < h) (L : ℕ) :
    Sexp ξ ρ L ≤ Real.exp (ξ * h) * F ξ h ^ (L / h) := by
  have hF0 : 0 ≤ F ξ h :=
    le_trans (avg_nonneg ξ 1 h 0) (avg_le_F ξ h ⟨le_rfl, zero_le_one⟩ (by simp))
  have h1 := iterate_bound (Sexp ξ ρ) hF0 hh (fun L hL => transfer ξ hξ hρ hL) L
  have h2 := Sexp_le_small ξ hρ (L % h)
  have h3 : Real.exp (|ξ| * (L % h : ℕ)) ≤ Real.exp (ξ * h) := by
    rw [abs_of_nonneg hξ]
    apply Real.exp_le_exp.2
    have : ((L % h : ℕ) : ℝ) ≤ h := by exact_mod_cast (Nat.mod_lt L hh).le
    exact mul_le_mul_of_nonneg_left this hξ
  have hp : 0 ≤ F ξ h ^ (L / h) := pow_nonneg hF0 _
  calc Sexp ξ ρ L ≤ Sexp ξ ρ (L % h) * F ξ h ^ (L / h) := h1
    _ ≤ Real.exp (ξ * h) * F ξ h ^ (L / h) :=
        mul_le_mul_of_nonneg_right (h2.trans h3) hp

/-- ASSEMBLY, CONDITIONAL ON the leaves of `Sexp_bound` and on `exp_markov`,
`TL_re_continuous`: for `h ≥ 1`, `ξ ≥ 0`, `|ρ| = 1`,
`meas{α ∈ [0,1] : Re(ρ T_L(α)) ≥ t} ≤ e^{-ξt} e^{ξh} F(ξ, h)^{[L/h]}`, Section 7, (42) with the
iteration. -/
theorem exceptional_bound {ξ : ℝ} (hξ : 0 ≤ ξ) {ρ : ℂ} (hρ : ‖ρ‖ = 1) {h : ℕ} (hh : 0 < h)
    (L : ℕ) (t : ℝ) :
    (volume {α ∈ Set.Icc (0 : ℝ) 1 | t ≤ (ρ * TL L α).re}).toReal ≤
      Real.exp (-(ξ * t)) * (Real.exp (ξ * h) * F ξ h ^ (L / h)) := by
  have hm := exp_markov (fun α => (ρ * TL L α).re) (TL_re_continuous L ρ) hξ t
  have hS := Sexp_bound hξ hρ hh L
  have hS' : ∫ α in (0 : ℝ)..1, Real.exp (ξ * (ρ * TL L α).re) = Sexp ξ ρ L := rfl
  rw [hS'] at hm
  have he : 0 < Real.exp (ξ * t) := Real.exp_pos _
  have key : (volume {α ∈ Set.Icc (0 : ℝ) 1 | t ≤ (ρ * TL L α).re}).toReal ≤
      Sexp ξ ρ L / Real.exp (ξ * t) := by
    rw [le_div_iff₀ he]; exact hm
  calc _ ≤ Sexp ξ ρ L / Real.exp (ξ * t) := key
    _ = Real.exp (-(ξ * t)) * Sexp ξ ρ L := by
        rw [Real.exp_neg]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le

end LeanLab.HeathBrownPuchta.Decomp1530a
