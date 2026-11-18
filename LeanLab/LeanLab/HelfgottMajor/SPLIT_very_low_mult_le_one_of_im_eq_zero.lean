import LeanLab.HelfgottMajor.SPLIT_book_count_band_very_low_mult_le
import LeanLab.HelfgottMajor.RealAxisBand
import LeanLab.PNTPort.DirichletZF.SiegelSigns

/-!
# Split of `very_low_mult_le_one_of_im_eq_zero` (`HelfgottMajor/SPLIT_book_count_band_very_low_mult_le`)

The target says that a strip zero of `L(·, χ)` whose imaginary part is zero has multiplicity at
most one, on the band `1 ≤ T`, `q * T ≤ 2πe`, for a primitive `χ`. The argument below reads a real
strip zero as a real number `σ` with `0 < σ < 1`, and it uses the symmetry of the completed
`L`-function about the line `Re s = 1/2` together with the simplicity of the zeros in the upper
half of the strip:

* `very_low_band_conductor_le_seventeen`: on the band the conductor is at most `17`, because the
  height is at least one. This reduces the claim to the finitely many characters of conductor at
  most `17`; it is the arithmetic half of the reduction, and it mentions neither `L` nor `mult`.
* `very_low_real_zero_reflect`: a real strip zero reflects to a real strip zero of the same
  multiplicity, `ρ ↦ 1 - ρ`. This is the symmetry step: `Λ(s) = Λ(1 - s)` up to a constant of
  modulus one, and the gamma factor does not vanish at a real point of `(0, 1)`, so the order of
  vanishing agrees at `ρ` and at `1 - ρ`.
* `very_low_real_zero_deriv_ne_zero_half`: in the upper half of the strip, a real strip zero is
  not a critical point of `L`. This is the only step that needs the zeros themselves, and with
  the conductor bound above it is a statement about finitely many `L`-functions.

The assembly splits on whether the real zero sits at height at least `1/2`. In the upper half it
is a critical point only if it is not simple, and the second leaf denies that. In the lower half
the reflected zero lies in the upper half, so the second leaf applies to it, and the first leaf
carries the multiplicity back. The passage from a non-vanishing derivative to a multiplicity at
most one is proved below, not assumed: a zero where the derivative does not vanish has order
exactly one.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Band arithmetic, the reduction to finitely many characters: on the band `1 ≤ T`,
`q * T ≤ 2πe` the conductor is at most `17`, since `1 ≤ T` gives `q ≤ q * T` and
`2πe < 18`. Nothing is asserted about zeros or multiplicities; the claim is only that the band
carries no character of conductor above seventeen. -/
theorem very_low_band_conductor_le_seventeen {T : ℝ} (hT : 1 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) : (q : ℝ) ≤ 17 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hqe : (q : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by
    have : (q : ℝ) * 1 ≤ (q : ℝ) * T := by nlinarith
    linarith
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h18 : 2 * Real.pi * Real.exp 1 < 18 := by nlinarith [hpi, he, hpi0, he0]
  have hq18 : (q : ℝ) < 18 := lt_of_le_of_lt hqe h18
  have hq18' : q < 18 := by exact_mod_cast hq18
  have : q ≤ 17 := by omega
  exact_mod_cast this

/-! ### Reflection of a strip zero under the functional equation.

The private lemmas below supply the symmetry of the completed `L`-function used by the leaf
`very_low_real_zero_reflect`: the Gamma factor is analytic and non-vanishing on the critical
strip, the functional equation of a primitive character reads the order of `L(·, χ)` at `ρ` off
the order of `L(·, χ⁻¹)` at `1 - ρ`, and the conjugation symmetry of `ZeroCount1623` closes the
circle back to `χ`. -/

omit [NeZero q] in
/-- The Gamma factor of the functional equation does not vanish on the right of the imaginary
axis, in particular on the open critical strip. -/
private lemma vlow_gammaFactor_ne_zero (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  classical
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith

/-- The Gamma factor of the functional equation is analytic on the right of the imaginary axis. -/
private lemma vlow_gammaFactor_analyticAt (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ χ.gammaFactor s := by
  classical
  have hinv : AnalyticAt ℂ (fun z => (χ.gammaFactor z)⁻¹) s := by
    apply Differentiable.analyticAt
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.differentiable_Gammaℝ_inv
    · exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
  have h := hinv.inv (inv_ne_zero (vlow_gammaFactor_ne_zero χ hs))
  have he : (fun z => (χ.gammaFactor z)⁻¹)⁻¹ = χ.gammaFactor := by
    funext z
    simp only [Pi.inv_apply, inv_inv]
  rwa [he] at h

/-- The functional equation reflects a strip zero of a primitive character to its inverse: a
zero `ρ` of `L(·, χ)` in the open strip is a zero of `L(·, χ⁻¹)` at `1 - ρ`. -/
private lemma vlow_primitive_zero_reflection (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    simp [h] at h0
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 := by
    have h := χ.LFunction_eq_completed_div_gammaFactor ρ (Or.inl hρ0)
    rw [hρ] at h
    exact (div_eq_zero_iff).mp h.symm |>.resolve_right (vlow_gammaFactor_ne_zero χ h0)
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have he := hi.completedLFunction_one_sub ρ
  simp only [inv_inv, hc, mul_zero] at he
  have hr : 1 - ρ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inl hr), he, zero_div]

/-- One half of the order reflection: the order of `L(·, χ)` at a strip point `ρ` is at most the
order of `L(·, χ⁻¹)` at `1 - ρ`, read off the functional equation. -/
private lemma vlow_primitive_order_reflection_le (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≤
      analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  let H : ℂ → ℂ := fun s => (q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ⁻¹ *
    χ.gammaFactor s * (χ⁻¹.gammaFactor (1 - s))⁻¹
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at h1
  have hH : AnalyticAt ℂ H ρ := by
    have hpow : AnalyticAt ℂ (fun s : ℂ => (q : ℂ) ^ (s - 1 / 2)) ρ := by
      apply Differentiable.analyticAt
      intro s
      exact (differentiableAt_id.sub_const _).const_cpow (Or.inl hq)
    have hg2 : AnalyticAt ℂ (fun s : ℂ => (χ⁻¹.gammaFactor (1 - s))⁻¹) ρ := by
      classical
      apply Differentiable.analyticAt
      unfold DirichletCharacter.gammaFactor
      split_ifs
      · exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.const_sub 1)
      · exact Complex.differentiable_Gammaℝ_inv.comp
          ((differentiable_id.const_sub 1).add_const 1)
    exact ((hpow.mul analyticAt_const).mul (vlow_gammaFactor_analyticAt χ h0)).mul hg2
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
    have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {(1 : ℂ)}ᶜ := fun s hs =>
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hρ1)
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 ρ]
      H * DirichletCharacter.LFunction χ := by
    filter_upwards [hopen.mem_nhds (show ρ ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} from ⟨h0, h1⟩)]
      with s hs
    have hs0 : s ≠ 0 := by
      intro h
      have := hs.1
      simp [h] at this
    have hr : 1 - s ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith [hs.2]
    have hg := vlow_gammaFactor_ne_zero χ hs.1
    have hc : DirichletCharacter.completedLFunction χ s =
        DirichletCharacter.LFunction χ s * χ.gammaFactor s := by
      rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0), div_mul_cancel₀ _ hg]
    have he := hi.completedLFunction_one_sub s
    rw [inv_inv] at he
    simp only [Function.comp_apply, Pi.mul_apply, H]
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inl hr), he, hc,
      div_eq_mul_inv]
    ring
  have hcomp : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) ρ =
      analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
    have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ :=
      (differentiable_id.const_sub (1 : ℂ)).analyticAt ρ
    have hd : deriv (fun s : ℂ => 1 - s) ρ ≠ 0 := by
      rw [deriv_const_sub, deriv_id'']
      norm_num
    exact analyticOrderAt_comp_of_deriv_ne_zero hg hd
  rw [← hcomp, analyticOrderAt_congr hev, analyticOrderAt_mul hH hL]
  exact le_add_self

/-- The functional equation keeps the multiplicity of a strip zero of a primitive character,
with the character inverted: `mult χ⁻¹ (1 - ρ) = mult χ ρ`. -/
private lemma vlow_primitive_mult_reflection (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    mult χ⁻¹ (1 - ρ) = mult χ ρ := by
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have ha := vlow_primitive_order_reflection_le χ hχ h0 h1
  have hb := vlow_primitive_order_reflection_le χ⁻¹ hi
    (ρ := 1 - ρ) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  rw [inv_inv, sub_sub_cancel] at hb
  unfold mult analyticOrderNatAt
  rw [le_antisymm hb ha]

/-- LEAF. Symmetry of the completed `L`-function at a real zero: a real strip zero `ρ` of a
primitive `χ` reflects to the real strip zero `1 - ρ` of the same `L`-function, with the same
multiplicity. The vanishing is carried by `Λ(s) = ε * Λ(1 - s)` with `|ε| = 1` together with the
non-vanishing of the gamma factor on the real axis inside the strip, and the multiplicity by the
non-vanishing of that factor, which makes the order of `Λ` at `ρ` the order of `L` at `ρ`. Only one
zero is treated at a time, and no bound on any multiplicity is asserted. -/
theorem very_low_real_zero_reflect (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    {ρ : ℂ} (hρ : ρ ∈ stripZeros χ T) (him : ρ.im = 0) :
    1 - ρ ∈ stripZeros χ T ∧ mult χ (1 - ρ) = mult χ ρ := by
  have hL : DirichletCharacter.LFunction χ ρ = 0 := hρ.1
  have h0 : 0 < ρ.re := hρ.2.1
  have h1 : ρ.re < 1 := hρ.2.2.1
  have hT0 : 0 ≤ T := le_trans (abs_nonneg ρ.im) hρ.2.2.2
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    norm_num at h1
  have h0' : 0 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h1' : (1 - ρ).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  -- conjugation fixes the real point, so the inverse character vanishes there too
  have hinv0 : DirichletCharacter.LFunction χ⁻¹ ρ = 0 := by
    have h := LFunction_inv_conj χ hρ1
    rw [Complex.conj_eq_iff_im.mpr him, hL] at h
    simpa using h
  have hinvprim : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have hvanish : DirichletCharacter.LFunction χ (1 - ρ) = 0 := by
    have h := vlow_primitive_zero_reflection (χ := χ⁻¹) hinvprim hinv0 h0 h1
    rwa [inv_inv] at h
  refine ⟨⟨hvanish, h0', h1', ?_⟩, ?_⟩
  · have him' : (1 - ρ).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im, him, sub_zero]
    rw [him']
    simpa using hT0
  · have hb : mult χ (1 - ρ) = mult χ⁻¹ ρ := by
      have h := vlow_primitive_mult_reflection (χ := χ⁻¹) hinvprim h0 h1
      rwa [inv_inv] at h
    rw [hb]
    calc mult χ⁻¹ ρ = mult χ⁻¹ (conj ρ) := by
          rw [Complex.conj_eq_iff_im.mpr him]
      _ = mult χ ρ := mult_inv_conj χ hρ1

/-- LEAF. Simplicity in the upper half, the only step that needs the zeros: for a primitive `χ`
of conductor at most `17`, a real strip zero with `1/2 ≤ Re ρ` is not a critical point of `L`,
that is `L'(ρ) ≠ 0`. The conductor bound is what makes this a statement about finitely many
`L`-functions; nothing is asserted about the lower half of the strip, and no multiplicity is
bounded here. -/
theorem very_low_real_zero_deriv_ne_zero_half (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : (q : ℝ) ≤ 17) {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ stripZeros χ T) (him : ρ.im = 0)
    (hhalf : 1 / 2 ≤ ρ.re) :
    deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
  -- The real point `ρ` is the coercion of `ρ.re`, and it is a zero of `L(·, χ)` there.
  have h0 : 0 < ρ.re := hρ.2.1
  have h1 : ρ.re < 1 := hρ.2.2.1
  have hcast : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hL : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by
    rw [← hcast]
    exact hρ.1
  have hq' : q ≤ 17 := by exact_mod_cast hq
  rcases eq_or_ne q 1 with hq1 | hq1
  · -- conductor one: the `L`-function is the zeta function, which is negative on `(0, 1)`
    subst hq1
    rw [DirichletCharacter.LFunction_modOne_eq] at hL
    have hneg := (LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg h0 h1).2
    rw [hL] at hneg
    simp at hneg
  · -- conductor at most seventeen and not one: no zero on the positive real axis at all
    exact absurd hL
      (LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_of_le_seventeen χ
        (LeanLab.HelfgottMajor.RealAxisKernel.ne_one_of_isPrimitive χ hχ hq1) hq' h0)

/-- A zero of `L(·, χ)` where the derivative does not vanish has order exactly one, hence
multiplicity at most one: the first two iterated derivatives are `L` itself, which vanishes, and
`L'`, which does not. -/
private lemma vlow_mult_le_one_of_deriv_ne_zero (χ : DirichletCharacter ℂ q) {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ stripZeros χ T) (hd : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0) :
    mult χ ρ ≤ 1 := by
  have hL : DirichletCharacter.LFunction χ ρ = 0 := hρ.1
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρ
    exact absurd hρ.2.2.1 (by norm_num)
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
      (fun s hs =>
        (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds hρ1)
  have hord : analyticOrderAt (DirichletCharacter.LFunction χ) ρ = ((1 : ℕ) : ℕ∞) := by
    rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han]
    refine ⟨fun k hk => ?_, ?_⟩
    · interval_cases k
      simpa using hL
    · simpa [iteratedDeriv_one] using hd
  have hone : mult χ ρ = 1 := by
    simp [mult, analyticOrderNatAt, hord]
  omega

/-- Assembly: a real strip zero on the band has multiplicity at most one. On the band the
conductor is at most `17`. A real zero at height at least `1/2` is not a critical point of `L`, so
its order is one. A real zero below `1/2` reflects to the real zero `1 - ρ` at height above
`1/2`, which is not a critical point either, and the multiplicities of the two agree. -/
theorem very_low_mult_le_one_of_im_eq_zero_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ ∈ stripZeros χ T, ρ.im = 0 → mult χ ρ ≤ 1 := by
  have hq : (q : ℝ) ≤ 17 := very_low_band_conductor_le_seventeen hT hband
  intro ρ hρ him
  by_cases hhalf : 1 / 2 ≤ ρ.re
  · exact vlow_mult_le_one_of_deriv_ne_zero χ hρ
      (very_low_real_zero_deriv_ne_zero_half χ hχ hq hρ him hhalf)
  · have hlt : ρ.re < 1 / 2 := lt_of_not_ge hhalf
    obtain ⟨hmem, heq⟩ := very_low_real_zero_reflect χ hχ hρ him
    have him' : (1 - ρ).im = 0 := by simp [him]
    have hhalf' : 1 / 2 ≤ (1 - ρ).re := by
      have hre : (1 - ρ).re = 1 - ρ.re := by simp
      rw [hre]
      linarith
    have hd := very_low_real_zero_deriv_ne_zero_half χ hχ hq hmem him' hhalf'
    have hle : mult χ (1 - ρ) ≤ 1 := vlow_mult_le_one_of_deriv_ne_zero χ hmem hd
    omega

end LeanLab.HelfgottMajor.ZeroCount1623
