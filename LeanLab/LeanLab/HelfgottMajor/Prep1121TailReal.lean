import LeanLab.HelfgottMajor.Prep1121TailRepair

/-!
burst-20261122, unit P1122-0057. P0014, Helfgott, Major arcs for Goldbach's problem,
arXiv 1305.2897v4, Lemma 4.5, page 41, display 4.33, the first display of the proof: the
pairing of a zero ρ with 1 - ρ.

`Prep1121TailRepair.tail_mass_bound_repaired` proves the tail bound for every primitive χ, but
without pairing, so with a factor 2 on the integral of display 4.35 and a factor 4 on the
boundary term. Here χ is REAL, stated as `χ ^ 2 = 1`. Then ρ ↦ 1 - ρ is an involution of the
tail zeros that preserves multiplicity, by the Mathlib functional equation
`DirichletCharacter.IsPrimitive.completedLFunction_one_sub` with χ⁻¹ = χ. So the tail sum of
`mellinMassTerm`, which is one sided, equals half of the sum of mult · (‖M(ρ)‖ + ‖M(1 - ρ)‖),
and hcor bounds each such pair. Every constant of the repaired bound is halved:
  sum ≤ 4.226 · (expTail + gaussTail) + 2 · 4.226 · tailEnv δ T · bookError q T.
This is exactly half of the repaired bound and no more: the pairing only removes the factor 2
that came from using hcor one sided. The boundary term of display 4.28 that the paper drops
stays, so this is still NOT the sealed `MainTail123.tail_mass_bound_leaf`.

Status: every lemma in this file is PROVED, CONDITIONAL ON hB and hcor as in the repaired file.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121TailReal
open Real MeasureTheory Filter Topology LeanLab.HelfgottArcs
open LeanLab.HelfgottMajor.SplitGaussian123 LeanLab.HelfgottMajor.Prep1121TailRepair

/-! ## The functional equation, from Mathlib -/

/-- PROVED. A real character, `χ ^ 2 = 1`, is its own inverse. -/
theorem inv_eq_self_of_sq {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : χ ^ 2 = 1) :
    χ⁻¹ = χ := by
  rw [pow_two] at hreal
  exact inv_eq_of_mul_eq_one_right hreal

/-- The open critical strip. -/
private theorem isOpen_strip : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- PROVED. The gamma factor does not vanish in the right half plane. -/
theorem gammaFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- PROVED. The inverse of the gamma factor is entire. -/
theorem differentiable_gammaFactor_inv {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (fun s => (DirichletCharacter.gammaFactor χ s)⁻¹) := by
  rcases χ.even_or_odd with h | h
  · simp_rw [h.gammaFactor_def]; exact Complex.differentiable_Gammaℝ_inv
  · simp_rw [h.gammaFactor_def]
    exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

/-- PROVED. The completed L-function is analytic in the open strip. -/
theorem analyticAt_completed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) s := by
  apply DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re ∧ s.re < 1})
  · intro z hz
    have h0 : z ≠ 0 := by intro h; simp [h] at hz
    have h1 : z ≠ 1 := by intro h; simp [h] at hz
    exact (DirichletCharacter.differentiableAt_completedLFunction χ z (Or.inl h0)
      (Or.inl h1)).differentiableWithinAt
  · exact isOpen_strip.mem_nhds hs

/-- PROVED. In the open strip, L equals the completed L-function times the inverse gamma
factor, near any point of the strip. -/
theorem LFunction_eventuallyEq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    DirichletCharacter.LFunction χ =ᶠ[𝓝 s] fun z =>
      DirichletCharacter.completedLFunction χ z * (DirichletCharacter.gammaFactor χ z)⁻¹ := by
  filter_upwards [isOpen_strip.mem_nhds hs] with z hz
  have h0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl h0), div_eq_mul_inv]

/-- PROVED. In the open strip, the analytic order of L equals that of the completed
L-function, since the gamma factor is analytic and nonzero there. -/
theorem order_LFunction_eq_completed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    analyticOrderAt (DirichletCharacter.LFunction χ) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) s := by
  rw [analyticOrderAt_congr (LFunction_eventuallyEq χ hs)]
  have hG : AnalyticAt ℂ (fun z => (DirichletCharacter.gammaFactor χ z)⁻¹) s :=
    (differentiable_gammaFactor_inv χ).analyticAt s
  have hG0 : analyticOrderAt (fun z => (DirichletCharacter.gammaFactor χ z)⁻¹) s = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero (gammaFactor_ne_zero χ hs.1)))
  have := analyticOrderAt_mul (analyticAt_completed χ hs) hG
  simp only [Pi.mul_def] at this
  rw [this, hG0, add_zero]

/-- PROVED. P0014 page 41, display 4.33, the functional equation for a primitive real χ:
the completed L-function at 1 - s is an entire multiple of its value at s. Mathlib
`completedLFunction_one_sub` with χ⁻¹ = χ. -/
theorem completed_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      ((q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ) *
        DirichletCharacter.completedLFunction χ s := by
  have h := hχ.completedLFunction_one_sub s
  rwa [inv_eq_self_of_sq hreal] at h

/-- PROVED. One direction of multiplicity symmetry: the order of the completed L-function at
1 - ρ is at least its order at ρ. -/
theorem order_completed_le_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hreal : χ ^ 2 = 1) {ρ : ℂ} (hρ : 0 < ρ.re ∧ ρ.re < 1) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≤
      analyticOrderAt (DirichletCharacter.completedLFunction χ) (1 - ρ) := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) ρ := by fun_prop
  have hg' : deriv (fun z : ℂ => 1 - z) ρ ≠ 0 := by
    rw [deriv_const_sub]; simp
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := DirichletCharacter.completedLFunction χ) hg hg'
  have he : (DirichletCharacter.completedLFunction χ ∘ fun z : ℂ => 1 - z) =
      (fun z : ℂ => (q : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ) *
        DirichletCharacter.completedLFunction χ := by
    funext z; simp only [Function.comp_apply, Pi.mul_apply]; exact completed_one_sub hχ hreal z
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hc : AnalyticAt ℂ
      (fun z : ℂ => (q : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ) ρ := by
    apply Differentiable.analyticAt
    intro z
    exact ((differentiableAt_id.sub_const _).const_cpow (Or.inl hq)).mul_const _
  rw [he, analyticOrderAt_mul hc (analyticAt_completed χ hρ)] at hcomp
  rw [← hcomp]
  exact le_add_self

/-- PROVED. P0014 page 41, display 4.33: for primitive real χ, the multiplicity of a zero ρ in
the open strip equals that of 1 - ρ. -/
theorem mult_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hreal : χ ^ 2 = 1) {ρ : ℂ} (hρ : 0 < ρ.re ∧ ρ.re < 1) :
    ZeroCount1623.mult χ (1 - ρ) = ZeroCount1623.mult χ ρ := by
  have hρ' : 0 < (1 - ρ).re ∧ (1 - ρ).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]; constructor <;> linarith [hρ.1, hρ.2]
  have h1 := order_completed_le_one_sub hχ hreal hρ
  have h2 := order_completed_le_one_sub hχ hreal hρ'
  rw [sub_sub_cancel] at h2
  simp only [ZeroCount1623.mult, analyticOrderNatAt]
  rw [order_LFunction_eq_completed χ hρ, order_LFunction_eq_completed χ hρ',
    le_antisymm h2 h1]

/-- PROVED. P0014 page 41, display 4.33: for primitive real χ, a zero ρ of L in the open strip
gives the zero 1 - ρ. -/
theorem LFunction_one_sub_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hreal : χ ^ 2 = 1) {ρ : ℂ} (hρ : 0 < ρ.re ∧ ρ.re < 1)
    (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ (1 - ρ) = 0 := by
  have h0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  have h0' : 1 - ρ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [hρ.2]
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl h0),
    div_eq_zero_iff] at hz
  have hΛ : DirichletCharacter.completedLFunction χ ρ = 0 := by
    rcases hz with h | h
    · exact h
    · exact absurd h (gammaFactor_ne_zero χ hρ.1)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ _ (Or.inl h0'),
    completed_one_sub hχ hreal, hΛ, mul_zero, zero_div]

/-! ## The involution of the tail zeros -/

/-- P0014 page 41, display 4.33: ρ ↦ 1 - ρ maps the tail zeros of a primitive real χ to
themselves. -/
def oneSubTail {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (T : ℝ) (ρ : TailIdx χ T) : TailIdx χ T :=
  ⟨1 - ρ.val, LFunction_one_sub_eq_zero hχ hreal ⟨ρ.property.2.1, ρ.property.2.2.1⟩
      ρ.property.1, by
    simp only [Complex.sub_re, Complex.one_re]; linarith [ρ.property.2.2.1], by
    simp only [Complex.sub_re, Complex.one_re]; linarith [ρ.property.2.1], by
    simpa [Complex.sub_im] using ρ.property.2.2.2⟩

/-- The pairing ρ ↦ 1 - ρ of display 4.33, page 41, as an equivalence of the tail zeros, an involution. -/
def oneSubEquiv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (T : ℝ) : TailIdx χ T ≃ TailIdx χ T where
  toFun := oneSubTail hχ hreal T
  invFun := oneSubTail hχ hreal T
  left_inv ρ := Subtype.ext (by simp [oneSubTail])
  right_inv ρ := Subtype.ext (by simp [oneSubTail])

/-- PROVED. P0014 page 41, display 4.33 with hcor, Corollary 3.2 at k equal to 0: the Mellin
mass of a pair ρ, 1 - ρ is at most 4.226 times the multiplicity times the majorant of display
4.34. -/
theorem pair_mass_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im)
    (ρ : TailIdx χ T) :
    mellinMassTerm χ δ ρ.val + mellinMassTerm χ δ (oneSubEquiv hχ hreal T ρ).val ≤
      4.226 * ((ZeroCount1623.mult χ ρ.val : ℝ) * tailEnv δ |ρ.val.im|) := by
  have hT' : max 100 (4 * π ^ 2 * |δ|) ≤ |ρ.val.im| := by
    rw [max_comm]; exact hT.trans ρ.property.2.2.2.le
  have h := hcor ρ.val ρ.property.2.1.le ρ.property.2.2.1.le hT'
  have hm := mult_one_sub hχ hreal ⟨ρ.property.2.1, ρ.property.2.2.1⟩
  have h2 := corEnvelope_le δ ρ.val.im
  have e : tailEnv δ |ρ.val.im| = exp (-0.1598 * |ρ.val.im|) +
      if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2) := rfl
  have hval : (oneSubEquiv hχ hreal T ρ).val = 1 - ρ.val := rfl
  have hmn : (0 : ℝ) ≤ (ZeroCount1623.mult χ ρ.val : ℝ) := Nat.cast_nonneg _
  unfold mellinMassTerm
  rw [hval]
  simp only [ZeroCount1623.mult] at hm hmn ⊢
  rw [hm, e]
  calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ +
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ (1 - ρ.val)‖
      = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (‖gaussianMellin δ ρ.val‖ + ‖gaussianMellin δ (1 - ρ.val)‖) := by ring
    _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (4.226 * corEnvelope δ ρ.val.im) := mul_le_mul_of_nonneg_left h hmn
    _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (4.226 * (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
        gcongr
    _ = _ := by ring

/-- PROVED. The pairing identity for a summable function and an equivalence of the index type:
twice the sum is the sum of f and f composed with the equivalence. -/
theorem two_mul_tsum_eq_tsum_add {ι : Type*} (σ : ι ≃ ι) {f : ι → ℝ} (hf : Summable f) :
    2 * ∑' i, f i = ∑' i, (f i + f (σ i)) := by
  have hfσ : Summable (fun i => f (σ i)) := (σ.summable_iff (f := f)).mpr hf
  rw [hf.tsum_add hfσ, σ.tsum_eq (f := f)]
  ring

/-! ## The paired bound -/

/-- PROVED, CONDITIONAL ON hB, the cited count of display 4.26, page 38, and on hcor, Corollary
3.2 at k equal to 0, page 10. P0014 Lemma 4.5, page 41, displays 4.33 to 4.35, REPAIRED and
PAIRED for primitive REAL χ: every constant of `tail_mass_bound_repaired` halves. The boundary
term of display 4.28 stays, so this is NOT the sealed `MainTail123.tail_mass_bound_leaf`. -/
theorem tail_mass_bound_repaired_real (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : TailIdx χ T => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : TailIdx χ T, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      2 * 4.226 * tailEnv δ T * ZeroCount1623.bookError q T := by
  have hT1 : (1 : ℝ) ≤ T := by have := (le_max_right _ _).trans hT; linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set U : ℝ → ℝ := fun t => 2 * (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T) +
    2 * (ZeroCount1623.bookError q t + ZeroCount1623.bookError q T) with hUdef
  obtain ⟨hgint, hGT⟩ := tailEnv_eq_integral δ hT0
  obtain ⟨hI1, hI2⟩ := ibp_integrable q δ hT1
  have hgU_eq : (fun t => tailEnvDeriv δ t * U t) =
      fun t => (2 * (tailEnvDeriv δ t * (ZeroCount1623.bookMain q t -
        ZeroCount1623.bookMain q T)) + 2 * (tailEnvDeriv δ t * ZeroCount1623.bookError q t)) +
          (2 * ZeroCount1623.bookError q T) * tailEnvDeriv δ t := by
    funext t; simp only [hUdef]; ring
  have hgU : IntegrableOn (fun t => tailEnvDeriv δ t * U t) (Set.Ioi T) := by
    rw [hgU_eq]
    exact ((hI1.const_mul 2).add (hI2.const_mul 2)).add
      (hgint.const_mul (2 * ZeroCount1623.bookError q T))
  have hU : ∀ t, T < t → twoSidedCount χ t - twoSidedCount χ T ≤ U t :=
    fun t ht => count_increment_le hB χ hχ hT1 ht.le
  obtain ⟨hsum, hle⟩ := layer_cake_le χ T (tailEnvDeriv δ) U
    (fun t ht => tailEnvDeriv_nonneg δ (hT0.trans ht.le)) hgint hU hgU
  set σ := oneSubEquiv hχ hreal T
  have hpt : ∀ ρ : TailIdx χ T, mellinMassTerm χ δ ρ.val + mellinMassTerm χ δ (σ ρ).val ≤
      4.226 * ((ZeroCount1623.mult χ ρ.val : ℝ) *
        ∫ t in Set.Ioi |ρ.val.im|, tailEnvDeriv δ t) := by
    intro ρ
    rw [← (tailEnv_eq_integral δ (abs_nonneg ρ.val.im)).2]
    exact pair_mass_le hχ hreal δ T hT hcor ρ
  have hsumM : Summable (fun ρ : TailIdx χ T => mellinMassTerm χ δ ρ.val) :=
    MainTail123.tail_mass_summable_of_book hB q χ hχ δ T hT hcor
  have hsumP : Summable (fun ρ : TailIdx χ T =>
      mellinMassTerm χ δ ρ.val + mellinMassTerm χ δ (σ ρ).val) :=
    hsumM.add ((σ.summable_iff (f := fun ρ : TailIdx χ T => mellinMassTerm χ δ ρ.val)).mpr hsumM)
  refine ⟨hsumM, ?_⟩
  have hint : ∫ t in Set.Ioi T, tailEnvDeriv δ t * U t =
      2 * (∫ t in Set.Ioi T, tailEnv δ t * mainDensity q t) +
        2 * (∫ t in Set.Ioi T, tailEnv δ t * (0.15 / t)) +
          4 * (tailEnv δ T * ZeroCount1623.bookError q T) := by
    have hA : IntegrableOn (fun t => 2 * (tailEnvDeriv δ t *
        (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T))) (Set.Ioi T) :=
      hI1.const_mul 2
    have hB2 : IntegrableOn (fun t => 2 * (tailEnvDeriv δ t * ZeroCount1623.bookError q t))
        (Set.Ioi T) := hI2.const_mul 2
    have hC : IntegrableOn (fun t => 2 * ZeroCount1623.bookError q T * tailEnvDeriv δ t)
        (Set.Ioi T) := hgint.const_mul _
    have hAB : IntegrableOn (fun t => 2 * (tailEnvDeriv δ t *
        (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T)) +
          2 * (tailEnvDeriv δ t * ZeroCount1623.bookError q t)) (Set.Ioi T) := hA.add hB2
    rw [hgU_eq, integral_add hAB hC, integral_add hA hB2,
      integral_const_mul, integral_const_mul, integral_const_mul, ← hGT,
      ibp_main q δ hT1, ibp_error q δ hT1]
    ring
  have hdens := density_integral_le q δ hT1
  rw [tailEnv_integral_split q δ hT1] at hdens
  have h2 : 2 * (∑' ρ : TailIdx χ T, mellinMassTerm χ δ ρ.val) ≤
      4.226 * ∫ t in Set.Ioi T, tailEnvDeriv δ t * U t := by
    rw [two_mul_tsum_eq_tsum_add σ hsumM]
    calc (∑' ρ : TailIdx χ T, (mellinMassTerm χ δ ρ.val + mellinMassTerm χ δ (σ ρ).val))
        ≤ ∑' ρ : TailIdx χ T, 4.226 * ((ZeroCount1623.mult χ ρ.val : ℝ) *
            ∫ t in Set.Ioi |ρ.val.im|, tailEnvDeriv δ t) :=
          hsumP.tsum_le_tsum hpt (hsum.mul_left 4.226)
      _ = 4.226 * ∑' ρ : TailIdx χ T, (ZeroCount1623.mult χ ρ.val : ℝ) *
            ∫ t in Set.Ioi |ρ.val.im|, tailEnvDeriv δ t := tsum_mul_left
      _ ≤ _ := by gcongr
  rw [hint] at h2
  linarith [hdens]

end LeanLab.HelfgottMajor.Prep1121TailReal

#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.tail_mass_bound_repaired_real
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.inv_eq_self_of_sq
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.gammaFactor_ne_zero
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.differentiable_gammaFactor_inv
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.analyticAt_completed
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.LFunction_eventuallyEq
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.order_LFunction_eq_completed
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.completed_one_sub
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.order_completed_le_one_sub
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.mult_one_sub
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.LFunction_one_sub_eq_zero
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.oneSubEquiv
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.pair_mass_le
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.two_mul_tsum_eq_tsum_add
#print axioms LeanLab.HelfgottMajor.Prep1121TailReal.oneSubTail
