import LeanLab.Linnik.ExplicitFormula.LeftHalf
import LeanLab.PNTPort.ExplicitPsi1.Residues

/-!
# Trivial zeros of a primitive `L(s, χ)` and their residues in the sharp kernel

Unit P1122-0016, ROUTE BURST burst-20261122 session S2, port step 5 of the half weighted
truncated explicit formula for primitive nonprincipal `χ`, Davenport, Multiplicative Number
Theory, second edition, chapter 19, pages 115 to 118. AI wrote the Lean code. Binary Goldbach
is OPEN; nothing here bears on it directly.

Let `χ` be primitive modulo `q`, `χ ≠ 1`, with parity `a`, `χ(-1) = (-1)^a`, `a ∈ {0, 1}`.
The sharp kernel integrand is `-(L'/L)(s, χ) xˢ/s`, written inline.

* `LFunction_eq_mul_trivial`: for every `k ≥ 0`, `L(s, χ) = (s + a + 2k) v(s)` with `v` entire
  and `v(-a - 2k) ≠ 0`; Davenport ch. 9, `Λ(s, χ) = (q/π)^{(s+a)/2} Γ((s+a)/2) L(s, χ)` with
  `Λ` nonvanishing on `Re s ≤ 0` by the functional equation.
* `LFunction_eq_zero_iff_of_re_nonpos`: on `Re s ≤ 0` the zeros are exactly `-a - 2k`,
  `k ≥ 0`; for `a = 0` this includes `s = 0`. `analyticOrderAt_trivial`: all are simple.
* `tendsto_mul_logDeriv_trivial`: `(s + m) L'/L(s) → 1` at `s = -m`, `m = a + 2k`.
* `residue_trivial_char`: the residue of the integrand at a trivial zero `-m`, `m > 0`, is
  `x^{-m}/m`, Davenport p. 115 display (2) and p. 116 display (3).
* `residue_zero_odd`: for `a = 1` the residue at `0` is `-L'(0, χ)/L(0, χ)`, p. 115 (2).
* `laurent_zero_even`: for `a = 0`, with `b(χ)` the constant term of `L'/L` at `0`, the
  coefficient of `1/s` of the integrand at `0` is `-(log x + b(χ))`, p. 116.
* `hasSum_trivial_even`, `hasSum_trivial_odd`, `trivial_sum_le`: the sums over the trivial zeros
  are `-(1/2) log(1 - x⁻²)` and `(1/2) log((1 + x⁻¹)/(1 - x⁻¹))`, both at most `1/(x - 1)`.
* LEAF `b_regroup_leaf`, HARD, see its doc for a cheaper route: Davenport p. 118, `b(χ) = -Σ_{|γ|<1} 1/ρ + O(log q)`.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122

open Complex Filter Topology Set
open scoped Real

/-- The gamma factor of `χ` with parity `a` is `Γℝ(s + a)`. Davenport ch. 9, p. 71. -/
theorem gammaFactor_eq_parity {q : ℕ} {χ : DirichletCharacter ℂ q} {a : ℕ}
    (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) (s : ℂ) :
    DirichletCharacter.gammaFactor χ s = Gammaℝ (s + a) := by
  rcases ha with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · rw [h.gammaFactor_def]; simp
  · rw [h.gammaFactor_def]; simp

/-- The Gamma recurrence iterated, valid at the poles as well:
`1/Γ(w) = w (w + 1) ... (w + k) / Γ(w + k + 1)`. -/
theorem inv_Gamma_eq_prod (k : ℕ) (w : ℂ) :
    (Gamma w)⁻¹ = (∏ j ∈ Finset.range (k + 1), (w + j)) * (Gamma (w + ((k : ℂ) + 1)))⁻¹ := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.prod_singleton, Nat.cast_zero, add_zero]
    exact one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w
  | succ k ih =>
    rw [ih, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (w + ((k : ℂ) + 1)),
      Finset.prod_range_succ _ (k + 1)]
    have e : w + ((k : ℂ) + 1) + 1 = w + (((k + 1 : ℕ) : ℂ) + 1) := by push_cast; ring
    rw [e]
    push_cast
    ring

/-- `χ ≠ 1` forces the modulus to differ from `1`. -/
lemma modulus_ne_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : q ≠ 1 :=
  hχ ∘ DirichletCharacter.level_one' χ

/-- Davenport ch. 9: `L(s, χ) = Λ(s, χ) / Γℝ(s + a)`, with Mathlib's convention that
`1/Γℝ` vanishes at the poles, valid for every `s`. -/
theorem LFunction_eq_completed_mul_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) (s : ℂ) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s * (Gammaℝ (s + a))⁻¹ := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr (modulus_ne_one hχ)),
    gammaFactor_eq_parity ha, div_eq_mul_inv]

/-- **The trivial zeros, factored.** Davenport ch. 9 and ch. 19 p. 115: for primitive
`χ ≠ 1` of parity `a` and every `k ≥ 0`, `L(s, χ) = (s + a + 2k) v(s)` with `v` entire and
`v(-a - 2k) ≠ 0`. For `a = 0`, `k = 0` this is the simple zero at `s = 0`. -/
theorem LFunction_eq_mul_trivial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) :
    ∃ v : ℂ → ℂ, Differentiable ℂ v ∧ v (-((a : ℂ) + 2 * k)) ≠ 0 ∧
      ∀ s, DirichletCharacter.LFunction χ s = (s + ((a : ℂ) + 2 * k)) * v s := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨fun s => DirichletCharacter.completedLFunction χ s *
      ((π : ℂ) ^ ((s + a) / 2) * ((∏ j ∈ Finset.range k, ((s + a) / 2 + j)) *
        ((1 / 2) * (Gamma ((s + a) / 2 + ((k : ℂ) + 1)))⁻¹))), ?_, ?_, ?_⟩
  · have hΛ := DirichletCharacter.differentiable_completedLFunction hχ
    have h1 : Differentiable ℂ fun s : ℂ => (s + a) / 2 :=
      (differentiable_id.add_const _).div_const _
    have hp : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ ((s + a) / 2) :=
      fun s => (h1 s).const_cpow (Or.inl hπ)
    have hprod : Differentiable ℂ fun s : ℂ => ∏ j ∈ Finset.range k, ((s + a) / 2 + j) := by
      fun_prop
    have hg : Differentiable ℂ fun s : ℂ => (Gamma ((s + a) / 2 + ((k : ℂ) + 1)))⁻¹ :=
      differentiable_one_div_Gamma.comp (h1.add_const _)
    exact hΛ.mul (hp.mul (hprod.mul (hg.const_mul _)))
  · have hre : (-((a : ℂ) + 2 * k)).re ≤ 0 := by
      rw [show (-((a : ℂ) + 2 * k)) = ((-((a : ℝ) + 2 * k) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
      have := (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    have hΛ := LeanLab.Linnik.ExplicitFormula.completed_ne_zero_of_re_nonpos hprim hre (Or.inr hχ)
    have hw : (-((a : ℂ) + 2 * k) + a) / 2 = -(k : ℂ) := by ring
    simp only [hw]
    refine mul_ne_zero hΛ (mul_ne_zero ?_ (mul_ne_zero ?_ (mul_ne_zero (by norm_num) ?_)))
    · exact cpow_ne_zero_iff.mpr (Or.inl hπ)
    · rw [Finset.prod_ne_zero_iff]
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      intro h
      have : ((j : ℤ) : ℂ) = ((k : ℤ) : ℂ) := by push_cast; linear_combination h
      have := Int.cast_injective this
      omega
    · rw [show -(k : ℂ) + ((k : ℂ) + 1) = 1 by ring, Gamma_one, inv_one]
      exact one_ne_zero
  · intro s
    rw [LFunction_eq_completed_mul_inv hχ ha, Gammaℝ_def, mul_inv, ← cpow_neg,
      show -(-(s + a) / 2) = (s + a) / 2 by ring, inv_Gamma_eq_prod k ((s + a) / 2),
      Finset.prod_range_succ]
    ring

/-- **The zeros on `Re s ≤ 0`.** Davenport ch. 19 p. 115 and ch. 9: for primitive `χ ≠ 1` of
parity `a`, a point with `Re s ≤ 0` is a zero of `L(s, χ)` exactly when `s = -a - 2k`,
`k ≥ 0`. For `a = 0` this includes `s = 0`. -/
theorem LFunction_eq_zero_iff_of_re_nonpos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    {s : ℂ} (hs : s.re ≤ 0) :
    DirichletCharacter.LFunction χ s = 0 ↔ ∃ k : ℕ, s = -((a : ℂ) + 2 * k) := by
  constructor
  · intro h0
    rw [LFunction_eq_completed_mul_inv hχ ha] at h0
    have hΛ := LeanLab.Linnik.ExplicitFormula.completed_ne_zero_of_re_nonpos hprim hs (Or.inr hχ)
    have hg : Gammaℝ (s + a) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hΛ
      · exact inv_eq_zero.mp h
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hg
    exact ⟨n, by linear_combination hn⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨v, -, -, hv⟩ := LFunction_eq_mul_trivial hprim hχ ha k
    rw [hv]; simp

/-- **The trivial zeros are simple.** Davenport ch. 19 p. 115: `L(s, χ)` has analytic order
exactly one at `s = -a - 2k` for every `k ≥ 0`. -/
theorem analyticOrderAt_trivial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) (-((a : ℂ) + 2 * k)) = 1 ∧
      analyticOrderNatAt (DirichletCharacter.LFunction χ) (-((a : ℂ) + 2 * k)) = 1 := by
  obtain ⟨v, hvd, hv0, hv⟩ := LFunction_eq_mul_trivial hprim hχ ha k
  set p : ℂ := -((a : ℂ) + 2 * k) with hp
  have hL : DirichletCharacter.LFunction χ = fun s => (s + ((a : ℂ) + 2 * k)) * v s := funext hv
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) p :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt p
  have hz : DirichletCharacter.LFunction χ p = 0 := by rw [hv, hp]; ring
  have hd : HasDerivAt (DirichletCharacter.LFunction χ) (1 * v p + (p + ((a : ℂ) + 2 * k)) *
      deriv v p) p := by
    rw [hL]
    exact ((hasDerivAt_id p).add_const _).mul (hvd p).hasDerivAt
  have hd' : deriv (DirichletCharacter.LFunction χ) p ≠ 0 := by
    have hp' : p + ((a : ℂ) + 2 * k) = 0 := by rw [hp]; ring
    rw [hd.deriv, hp']; simpa using hv0
  have ho := hA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd'
  exact ⟨ho, by simp [analyticOrderNatAt, ho]⟩

/-- Davenport ch. 19 p. 115: near a trivial zero `-m`, `m = a + 2k`,
`L'/L(s) = 1/(s + m) + v'/v(s)` with `v` from `LFunction_eq_mul_trivial`, so
`L'/L(s) - 1/(s + m)` has a finite limit. For `m = 0`, `a = 0`, the limit is the constant
`b(χ)` of p. 116. -/
theorem tendsto_logDeriv_sub_trivial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) :
    ∃ c : ℂ, Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / (s + ((a : ℂ) + 2 * k)))
      (𝓝[≠] (-((a : ℂ) + 2 * k))) (𝓝 c) := by
  obtain ⟨v, hvd, hv0, hv⟩ := LFunction_eq_mul_trivial hprim hχ ha k
  set p : ℂ := -((a : ℂ) + 2 * k) with hp
  have hL : DirichletCharacter.LFunction χ = fun s => (s + ((a : ℂ) + 2 * k)) * v s := funext hv
  have hva : AnalyticAt ℂ v p := hvd.analyticAt p
  refine ⟨deriv v p / v p, ?_⟩
  have hc : ContinuousAt (fun s => deriv v s / v s) p :=
    hva.deriv.continuousAt.div hva.continuousAt hv0
  have hne : ∀ᶠ s in 𝓝 p, v s ≠ 0 := hva.continuousAt.eventually_ne hv0
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds hne, self_mem_nhdsWithin] with s hs hsp
  have hsm : s + ((a : ℂ) + 2 * k) ≠ 0 := by
    intro h; apply hsp; show s = p; rw [hp]; linear_combination h
  have hd : deriv (DirichletCharacter.LFunction χ) s =
      1 * v s + (s + ((a : ℂ) + 2 * k)) * deriv v s := by
    rw [hL]; exact (((hasDerivAt_id s).add_const _).mul (hvd s).hasDerivAt).deriv
  rw [hd, hL]
  field_simp
  ring

/-- **Residue of `L'/L` at a trivial zero.** Davenport ch. 19 p. 115:
`(s + m) L'/L(s) → 1` as `s → -m`, `m = a + 2k`, the trivial zeros being simple. -/
theorem tendsto_mul_logDeriv_trivial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) :
    Tendsto (fun s => (s + ((a : ℂ) + 2 * k)) * (deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)) (𝓝[≠] (-((a : ℂ) + 2 * k))) (𝓝 1) := by
  obtain ⟨c, hc⟩ := tendsto_logDeriv_sub_trivial hprim hχ ha k
  set p : ℂ := -((a : ℂ) + 2 * k) with hp
  have h0 : Tendsto (fun s : ℂ => s + ((a : ℂ) + 2 * k)) (𝓝[≠] p) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s + ((a : ℂ) + 2 * k)) (𝓝 p) (𝓝 (p + ((a : ℂ) + 2 * k))) :=
      (continuous_id.add continuous_const).tendsto p
    rw [hp, neg_add_cancel] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := (h0.mul hc).const_add 1
  rw [zero_mul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hsp
  have hsm : s + ((a : ℂ) + 2 * k) ≠ 0 := by
    intro h; apply hsp; show s = p; rw [hp]; linear_combination h
  field_simp
  ring

/-- **Residue at a trivial zero.** Davenport ch. 19 p. 115 display (2) and p. 116 display (3):
for `x > 0` and a trivial zero `-m`, `m = a + 2k > 0`, the residue of the sharp kernel integrand
`-(L'/L)(s, χ) xˢ/s` is `x^{-m}/m`. -/
theorem residue_trivial_char {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) (hm : a + 2 * k ≠ 0) {x : ℝ} (hx : 0 < x) :
    residue (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) (-((a : ℂ) + 2 * k)) =
      (x : ℂ) ^ (-((a : ℂ) + 2 * k)) / ((a : ℂ) + 2 * k) := by
  set p : ℂ := -((a : ℂ) + 2 * k) with hp
  have hp0 : p ≠ 0 := by
    rw [hp, neg_ne_zero]
    have : ((a + 2 * k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    simpa using this
  apply residue_eq_of_tendsto
  have hk : Tendsto (fun s : ℂ => (x : ℂ) ^ s / s) (𝓝[≠] p) (𝓝 ((x : ℂ) ^ p / p)) :=
    (((analyticAt_xpow hx p).div analyticAt_id hp0).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have h := ((tendsto_mul_logDeriv_trivial hprim hχ ha k).mul hk).neg
  have hv : -(1 * ((x : ℂ) ^ p / p)) = (x : ℂ) ^ p / ((a : ℂ) + 2 * k) := by
    rw [hp]; field_simp
  rw [hv] at h
  refine h.congr' (Eventually.of_forall fun s => ?_)
  ring

/-- **Residue at `0`, odd case.** Davenport ch. 19 p. 115 display (2): for `a = 1`,
`L(0, χ) ≠ 0` and the residue of `-(L'/L)(s, χ) xˢ/s` at `0` is `-L'(0, χ)/L(0, χ)`. -/
theorem residue_zero_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hodd : χ.Odd) {x : ℝ} (hx : 0 < x) :
    DirichletCharacter.LFunction χ 0 ≠ 0 ∧
    residue (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) 0 =
      -(deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0) := by
  have ha : (χ.Even ∧ (1 : ℕ) = 0) ∨ (χ.Odd ∧ (1 : ℕ) = 1) := Or.inr ⟨hodd, rfl⟩
  have hL0 : DirichletCharacter.LFunction χ 0 ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := (LFunction_eq_zero_iff_of_re_nonpos hprim hχ ha (by simp)).mp h
    have := congr_arg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine ⟨hL0, ?_⟩
  apply residue_eq_of_tendsto
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 0 :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt 0
  have hH : ContinuousAt (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s) 0 :=
    ((hA.deriv.continuousAt.div hA.continuousAt hL0).neg).mul
      (analyticAt_xpow hx 0).continuousAt
  have ht := hH.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  simp only [cpow_zero, mul_one] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  rw [sub_zero]
  field_simp

/-- **The constant `b(χ)` exists, even case.** Davenport ch. 19 p. 116: for `a = 0` the zero
at `0` is simple, so `L'/L(s) = 1/s + b(χ) + O(s)`; here `b(χ)` is the limit of
`L'/L(s) - 1/s`. -/
theorem exists_b_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even) :
    ∃ b : ℂ, Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b) := by
  obtain ⟨c, hc⟩ := tendsto_logDeriv_sub_trivial hprim hχ
    (a := 0) (Or.inl ⟨heven, rfl⟩) 0
  refine ⟨c, ?_⟩
  simpa using hc

/-- **The double pole at `0`, even case.** Davenport ch. 19 p. 116: for `a = 0` and `x > 0`,
with `b(χ)` the constant term of `L'/L` at `0`, `s · (-(L'/L)(s, χ) xˢ/s) + 1/s →
-(log x + b(χ))`: the coefficient of `1/s` in the Laurent expansion of the integrand at `0` is
`-(log x + b(χ))`, from `xˢ/s = 1/s + log x + ...`. -/
theorem laurent_zero_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {b : ℂ} (hb : Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b)) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s => s * (-(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) + 1 / s) (𝓝[≠] 0)
      (𝓝 (-((Real.log x : ℂ) + b))) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hD : HasDerivAt (fun s : ℂ => (x : ℂ) ^ s) ((x : ℂ) ^ (0 : ℂ) * Complex.log x * 1) 0 :=
    (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hx0)
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (ofReal_log hx.le).symm
  rw [cpow_zero, one_mul, mul_one, hlog] at hD
  have hslope := hD.tendsto_slope_zero
  simp only [zero_add, cpow_zero, smul_eq_mul] at hslope
  have hxs : Tendsto (fun s : ℂ => (x : ℂ) ^ s) (𝓝[≠] 0) (𝓝 1) := by
    have := ((analyticAt_xpow hx 0).continuousAt.tendsto).mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa using this
  have h := ((hb.mul hxs).neg).sub hslope
  rw [mul_one, show -b - (Real.log x : ℂ) = -((Real.log x : ℂ) + b) by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  field_simp
  ring

/-- The same statement with the lab's `residue`: after removing the principal part `-1/s²`,
the residue of the sharp kernel integrand at `0` is `-(log x + b(χ))`, Davenport ch. 19
p. 116. -/
theorem residue_zero_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {b : ℂ} (hb : Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b)) {x : ℝ} (hx : 0 < x) :
    residue (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s + 1 / s ^ 2) 0 =
      -((Real.log x : ℂ) + b) := by
  apply residue_eq_of_tendsto
  refine (laurent_zero_even hb hx).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  rw [sub_zero]
  field_simp

/-! ### The sums over the trivial zeros, Davenport ch. 19 p. 115 (2) and p. 116 (3) -/

/-- The residue `x^{-n}/n` is the real number `x⁻ⁿ/n`. -/
lemma trivial_term_eq (x : ℝ) (n : ℕ) :
    (x : ℂ) ^ (-(n : ℂ)) / (n : ℂ) = (((x⁻¹) ^ n / n : ℝ) : ℂ) := by
  rw [cpow_neg, cpow_natCast]
  push_cast
  rw [inv_pow]

/-- The even case: `Σ_{k ≥ 0} x^{-(2k+2)}/(2k+2) = -(1/2) log(1 - x⁻²)` for `x > 1`. -/
theorem hasSum_trivial_even_real {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x⁻¹) ^ (2 * k + 2) / ((2 * k + 2 : ℕ) : ℝ))
      (-(1 / 2) * Real.log (1 - (x⁻¹) ^ 2)) := by
  have hu0 : 0 < x⁻¹ := inv_pos.mpr (by linarith)
  have hu1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hy : |(x⁻¹) ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hy).mul_left (1 / 2)
  rw [show (1 / 2 : ℝ) * -Real.log (1 - (x⁻¹) ^ 2) = -(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) by
    ring] at h
  convert h using 1
  funext k
  rw [← pow_mul, show 2 * (k + 1) = 2 * k + 2 by ring]
  push_cast
  field_simp

/-- The odd case: `Σ_{k ≥ 0} x^{-(2k+1)}/(2k+1) = (1/2)(log(1 + x⁻¹) - log(1 - x⁻¹))` for
`x > 1`. -/
theorem hasSum_trivial_odd_real {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x⁻¹) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
      ((1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹))) := by
  have hu0 : 0 < x⁻¹ := inv_pos.mpr (by linarith)
  have hu1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hy : |x⁻¹| < 1 := by rw [abs_of_pos hu0]; exact hu1
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hy).mul_left (1 / 2)
  convert h using 1
  funext k
  push_cast
  field_simp

/-- **The trivial zero series, even character.** Davenport ch. 19 p. 116 display (3):
for `x > 1`, `Σ_{k ≥ 0} x^{-(2k+2)}/(2k+2) = -(1/2) log(1 - x⁻²)`, the sum of the residues
`residue_trivial_char` at the trivial zeros `-2(k+1)` for `a = 0`. -/
theorem hasSum_trivial_even {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x : ℂ) ^ (-((0 : ℕ) + 2 * ((k + 1 : ℕ) : ℂ))) /
        ((0 : ℕ) + 2 * ((k + 1 : ℕ) : ℂ)))
      ((-(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) : ℝ) : ℂ) := by
  refine (Complex.hasSum_ofReal.mpr (hasSum_trivial_even_real hx)).congr_fun ?_
  intro k
  have e : ((0 : ℕ) : ℂ) + 2 * ((k + 1 : ℕ) : ℂ) = ((2 * k + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [e, trivial_term_eq x]

/-- **The trivial zero series, odd character.** Davenport ch. 19 p. 115 display (2):
for `x > 1`, `Σ_{k ≥ 0} x^{-(2k+1)}/(2k+1) = (1/2)(log(1 + x⁻¹) - log(1 - x⁻¹))`, the sum of the
residues `residue_trivial_char` at the trivial zeros `-(1 + 2k)` for `a = 1`. -/
theorem hasSum_trivial_odd {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x : ℂ) ^ (-((1 : ℕ) + 2 * (k : ℂ))) / ((1 : ℕ) + 2 * (k : ℂ)))
      (((1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹)) : ℝ) : ℂ) := by
  refine (Complex.hasSum_ofReal.mpr (hasSum_trivial_odd_real hx)).congr_fun ?_
  intro k
  have e : ((1 : ℕ) : ℂ) + 2 * (k : ℂ) = ((2 * k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [e, trivial_term_eq x]

/-- Geometric majorant: `Σ_{k ≥ 0} x^{-(k+1)} = 1/(x - 1)` for `x > 1`. -/
lemma hasSum_geom_shift {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x⁻¹) ^ (k + 1)) (1 / (x - 1)) := by
  have hu0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (by linarith)
  have hu1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have h := (hasSum_geometric_of_lt_one hu0 hu1).mul_left x⁻¹
  have hx0 : x ≠ 0 := by positivity
  have hx1 : x - 1 ≠ 0 := by linarith
  have hv : x⁻¹ * (1 - x⁻¹)⁻¹ = 1 / (x - 1) := by
    field_simp
  rw [hv] at h
  refine h.congr_fun (fun k => ?_)
  ring

/-- **The trivial zero sums are `O(1)`.** Davenport ch. 19 p. 117, the sum over `m` absorbed
into the error term: for `x > 1` both trivial zero sums lie in `[0, 1/(x - 1)]`, so in
`[0, 1]` for `x ≥ 2`. -/
theorem trivial_sum_le {x : ℝ} (hx : 1 < x) :
    (0 ≤ -(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) ∧
      -(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) ≤ 1 / (x - 1)) ∧
    (0 ≤ (1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹)) ∧
      (1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹)) ≤ 1 / (x - 1)) := by
  have hu0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (by linarith)
  have hu1 : x⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hx).le
  have hg := hasSum_geom_shift hx
  have hterm : ∀ n j : ℕ, j + 1 ≤ n → 1 ≤ n → (x⁻¹) ^ n / (n : ℝ) ≤ (x⁻¹) ^ (j + 1) := by
    intro n j hjn hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc (x⁻¹) ^ n / (n : ℝ) ≤ (x⁻¹) ^ n := div_le_self (by positivity) hn'
      _ ≤ (x⁻¹) ^ (j + 1) := pow_le_pow_of_le_one hu0 hu1 hjn
  have hE := hasSum_trivial_even_real hx
  have hO := hasSum_trivial_odd_real hx
  refine ⟨⟨hasSum_le (fun k => by positivity) hasSum_zero hE, hasSum_le (fun k => ?_) hE hg⟩,
    ⟨hasSum_le (fun k => by positivity) hasSum_zero hO, hasSum_le (fun k => ?_) hO hg⟩⟩
  · exact hterm _ k (by omega) (by omega)
  · exact hterm _ k (by omega) (by omega)

/-! ### The constant `b(χ)`, Davenport ch. 19 p. 118 -/

/- Route notes for `b_regroup_leaf`. Davenport's route needs the Hadamard partial fraction (17)
of ch. 12 for `L'/L` at `s` and at `2`, the regularity of `Γ'/Γ` at `0` for `a = 1` and its
expansion `-1/s + const` for `a = 0`, and the zero count (3) of ch. 16 at `t = 0`, namely
`N(t + 1, χ) - N(t, χ) = O(log q(|t| + 2))`, which bounds the number of terms of the sum.
Alternative route: for even `χ` the lab already has `b` in closed form, from the functional
equation, as `log(2π/q) + γ - conj(L'/L(1, χ))`, in `PNTPort/LeftHalf` and
`HelfgottMajor/LogResidue669`; a local expansion of `L'/L` near `s = 1` together with the zero
count above may then suffice in place of the full Hadamard product, and similarly for odd `χ`
via the functional equation at `s = 0` and `s = 1`. -/

/-- LEAF: Davenport, Multiplicative Number Theory, second edition, ch. 19 p. 118, the display
`b(χ) = O(log q) - Σ_{|γ|<1} 1/ρ` following display (8). Class HARD, possibly cheaper by the
alternative route in the comment above. For primitive `χ ≠ 1`, `b(χ)` is `L'(0, χ)/L(0, χ)`
when `χ` is odd and the constant term of `L'/L` at `0` when `χ` is even, and
`b(χ) + Σ_{|γ|<1} m(ρ)/ρ = O(log q)` uniformly, the sum over the zeros with `0 < Re ρ < 1`,
`m(ρ)` the multiplicity. Note `q ≥ 3` here, so `log q > 1`. -/
theorem b_regroup_leaf : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ b : ℂ,
      ((χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
          DirichletCharacter.LFunction χ 0) ∨
        (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b))) →
      ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) →
      ‖b + ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ‖ ≤
        C * Real.log q := by
  sorry

end LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122

#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.gammaFactor_eq_parity
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.inv_Gamma_eq_prod
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.LFunction_eq_completed_mul_inv
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.LFunction_eq_mul_trivial
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.LFunction_eq_zero_iff_of_re_nonpos
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.analyticOrderAt_trivial
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.tendsto_logDeriv_sub_trivial
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.tendsto_mul_logDeriv_trivial
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.residue_trivial_char
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.residue_zero_odd
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.exists_b_even
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.laurent_zero_even
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.residue_zero_even
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.trivial_term_eq
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.hasSum_trivial_even_real
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.hasSum_trivial_odd_real
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.hasSum_trivial_even
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.hasSum_trivial_odd
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.hasSum_geom_shift
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.trivial_sum_le
#print axioms LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122.b_regroup_leaf
