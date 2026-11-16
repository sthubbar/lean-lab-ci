import LeanLab.HelfgottMajor.SPLIT_book_count_band_very_low_mult_le

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

/-- LEAF. Symmetry of the completed `L`-function at a real zero: a real strip zero `ρ` of a
primitive `χ` reflects to the real strip zero `1 - ρ` of the same `L`-function, with the same
multiplicity. The vanishing is carried by `Λ(s) = ε * Λ(1 - s)` with `|ε| = 1` together with the
non-vanishing of the gamma factor on the real axis inside the strip, and the multiplicity by the
non-vanishing of that factor, which makes the order of `Λ` at `ρ` the order of `L` at `ρ`. Only one
zero is treated at a time, and no bound on any multiplicity is asserted. -/
theorem very_low_real_zero_reflect (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    {ρ : ℂ} (hρ : ρ ∈ stripZeros χ T) (him : ρ.im = 0) :
    1 - ρ ∈ stripZeros χ T ∧ mult χ (1 - ρ) = mult χ ρ := by
  sorry

/-- LEAF. Simplicity in the upper half, the only step that needs the zeros: for a primitive `χ`
of conductor at most `17`, a real strip zero with `1/2 ≤ Re ρ` is not a critical point of `L`,
that is `L'(ρ) ≠ 0`. The conductor bound is what makes this a statement about finitely many
`L`-functions; nothing is asserted about the lower half of the strip, and no multiplicity is
bounded here. -/
theorem very_low_real_zero_deriv_ne_zero_half (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : (q : ℝ) ≤ 17) {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ stripZeros χ T) (him : ρ.im = 0)
    (hhalf : 1 / 2 ≤ ρ.re) :
    deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
  sorry

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
