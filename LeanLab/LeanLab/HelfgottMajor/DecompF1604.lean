import LeanLab.HelfgottMajor.DecompF547

/-!
Split of the pairing step `paired_mass_le` of DecompF547.lean, FREE-nv-glm7 task1604.
No existing file is edited.

The target bounds the two sided multiplicity weighted Mellin mass of the strip zeros above
height T against 4.226 times the one sided envelope sum. The proof runs in three leaves.

1. Pointwise mass bound. For each strip zero above height T, the Mellin mass term is at most
the analytic multiplicity times 4.226 times the two branch envelope sum. This uses the
proved corollary of the saddle analysis for the Gaussian Mellin transform.
2. Two sided summability. The two sided mass sum is summable, from the pointwise bound and
the summability of the one sided envelope.
3. Pairing inequality. The two sided mass sum is at most 4.226 times the one sided envelope
sum, by splitting into positive and negative imaginary parts, pairing the negative part
with the positive part via complex conjugation, and applying the pointwise bound.

The assembly `paired_mass_le_F1604` has the statement of the target character for character
and is proved from the three leaves with no gap of its own. AI wrote this Lean code.
Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real

section DecompF1604

/-- LEAF. Pointwise mass bound. For each zero rho of L(s, chi) in the open critical strip
above height T, the multiplicity weighted Mellin mass term is at most the analytic
multiplicity times 4.226 times the two branch envelope sum exp of minus 0.1598 times
the absolute height plus, away from zero shift, exp of minus 0.1065 times the square of
the height over pi times abs delta. This is the single zero estimate that drives the
whole pairing step. -/
theorem leaf_pointwise_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}) :
    mellinMassTerm χ δ ρ.val ≤
      (ZeroCount1623.mult χ ρ.val : ℝ) *
        (Real.exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) := by
  sorry


/-- Norm of a Dirichlet character value at a unit is one: the value is a root of unity. -/
private lemma norm_apply_unit {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (u : (ZMod M)ˣ) : ‖ψ (u : ZMod M)‖ = 1 := by
  have hcoe : ((ψ.toUnitHom u : ℂˣ) : ℂ) = ψ (u : ZMod M) := MulChar.coe_toUnitHom ψ u
  have h1 : ψ.toUnitHom u ^ Fintype.card (ZMod M)ˣ = 1 := by
    rw [← map_pow, pow_card_eq_one (x := u), map_one]
  have hpow : ((ψ.toUnitHom u : ℂˣ) : ℂ) ^ Fintype.card (ZMod M)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have hnorm : ‖((ψ.toUnitHom u : ℂˣ) : ℂ)‖ ^ Fintype.card (ZMod M)ˣ = 1 := by
    rw [← norm_pow, hpow, norm_one]
  have hcard : Fintype.card (ZMod M)ˣ ≠ 0 := (Fintype.card_pos (α := (ZMod M)ˣ)).ne'
  rw [← hcoe]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hcard).mp hnorm

/-- One Euler factor of a character of level `M` does not vanish in the open strip: at a prime
dividing the level the character value is zero, and otherwise the factor vanishes only where
`‖p^{-s}‖ = 1`, that is on the imaginary axis. -/
private lemma euler_factor_ne_zero {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (h0 : 0 < s.re) (_h1 : s.re < 1) :
    1 - ψ (p : ZMod M) * (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  by_cases hdvd : p ∣ M
  · have hnu : ¬ IsUnit ((p : ZMod M)) := by
      rw [ZMod.isUnit_prime_iff_not_dvd hp]; exact not_not.mpr hdvd
    rw [MulChar.map_nonunit ψ hnu, zero_mul, sub_zero] at hzero
    exact one_ne_zero hzero
  · have hu : IsUnit ((p : ZMod M)) := (ZMod.isUnit_prime_iff_not_dvd hp).mpr hdvd
    have hψ1 : ‖ψ (p : ZMod M)‖ = 1 := by
      simpa only [hu.unit_spec] using norm_apply_unit ψ hu.unit
    have hcv : ((p : ℝ) : ℂ) = (p : ℂ) := by push_cast; ring
    have hmul : ψ (p : ZMod M) * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
    have hn := congrArg norm hmul
    rw [norm_mul, hψ1, one_mul, ← hcv,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos : (0 : ℝ) < (p : ℝ)),
      Complex.neg_re, norm_one] at hn
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hlt : (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) := by
      rw [Real.rpow_lt_rpow_left_iff hp1]; linarith
    rw [Real.rpow_zero] at hlt
    linarith

/-- The finite Euler product of the induced level is nonzero in the open strip. -/
private lemma euler_prod_ne_zero {M q : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    (∏ p ∈ q.primeFactors, (1 - ψ (p : ZMod M) * (p : ℂ) ^ (-s))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact euler_factor_ne_zero ψ p (Nat.mem_primeFactors.mp hp).1 s h0 h1

/-- The finite Euler product of the induced level is analytic. -/
private lemma analyticAt_euler_prod {M q : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors,
      (1 - ψ (p : ZMod M) * (p : ℂ) ^ (-z))) s := by
  have hd : ∀ z : ℂ, DifferentiableAt ℂ (fun w : ℂ => ∏ p ∈ q.primeFactors,
      (1 - ψ (p : ZMod M) * (p : ℂ) ^ (-w))) z := by
    intro z
    refine .fun_finsetProd (fun p hp => ?_)
    have hp' : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hc : (p : ℂ) ≠ 0 := by
      have h0 : (0 : ℕ) < p := hp'.pos
      exact_mod_cast h0.ne'
    have hc' : DifferentiableAt ℂ (fun w : ℂ => (p : ℂ) ^ (-w)) z :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl hc)
    have h1 : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) z := differentiableAt_const _
    have h2 : DifferentiableAt ℂ (fun _ : ℂ => ψ (p : ZMod M)) z := differentiableAt_const _
    exact DifferentiableAt.sub h1 (DifferentiableAt.mul h2 hc')
  refine DifferentiableOn.analyticAt (s := Set.univ) (fun z _ => (hd z).differentiableWithinAt) ?_
  exact Filter.univ_mem

/-- LEAF. Two sided summability. The multiplicity weighted Mellin mass of the strip zeros
above height T, taken over both signs of the imaginary part, is summable. This follows
from the pointwise mass bound and the summability of the one sided envelope sum, which
in turn follows from the exponential and Gaussian decay against the zero density. -/
theorem leaf_two_sided_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) := by
  classical
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter with hψ
  set E : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors,
    (1 - ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-z)) with hEdef
  have hψprim : ψ.IsPrimitive := by
    rw [hψ]; exact DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hfactor : ∀ z : ℂ, z ≠ 1 → DirichletCharacter.LFunction χ z =
      DirichletCharacter.LFunction ψ z * E z := by
    intro z hz
    have hch : DirichletCharacter.changeLevel χ.conductor_dvd_level ψ = χ := by
      rw [hψ]; exact DirichletCharacter.changeLevel_primitiveCharacter χ
    have h := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level ψ (Or.inr hz)
    rw [hch] at h
    rw [h, hEdef]
  have hEan : ∀ z : ℂ, AnalyticAt ℂ E z := by
    intro z; rw [hEdef]; exact analyticAt_euler_prod ψ z
  have hEne : ∀ z : ℂ, 0 < z.re → z.re < 1 → E z ≠ 0 := by
    intro z h0 h1; rw [hEdef]; exact euler_prod_ne_zero ψ z h0 h1
  have hmult : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      ZeroCount1623.mult χ ρ = ZeroCount1623.mult ψ ρ := by
    intro ρ h0 h1
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
    have hψan : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) ρ :=
      (by
        refine DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ)) ?_ ?_
        · intro w hw
          exact (DirichletCharacter.differentiableAt_LFunction ψ w (Or.inl hw)).differentiableWithinAt
        · exact isOpen_compl_singleton.mem_nhds hρ1)
    have hev : DirichletCharacter.LFunction χ =ᶠ[nhds ρ]
        (DirichletCharacter.LFunction ψ * E) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hρ1] with z hz
      exact hfactor z hz
    have horders : analyticOrderAt (DirichletCharacter.LFunction χ) ρ =
        analyticOrderAt (DirichletCharacter.LFunction ψ) ρ := by
      rw [analyticOrderAt_congr hev]
      by_cases htop : analyticOrderAt (DirichletCharacter.LFunction ψ) ρ = ⊤
      · rw [analyticOrderAt_mul_eq_top_of_left htop, htop]
      · have hE0 : analyticOrderAt E ρ = 0 :=
          ((hEan ρ).analyticOrderAt_eq_zero).mpr (hEne ρ h0 h1)
        rw [analyticOrderAt_mul hψan (hEan ρ), hE0, add_zero]
    exact congrArg ENat.toNat horders
  have hzero : ∀ ρ : ℂ, (DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|) ↔
      (DirichletCharacter.LFunction ψ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|) := by
    intro ρ
    have hstrip : 0 < ρ.re → ρ.re < 1 → (DirichletCharacter.LFunction χ ρ = 0 ↔
        DirichletCharacter.LFunction ψ ρ = 0) := by
      intro h0 h1
      have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
      rw [hfactor ρ hρ1, mul_eq_zero]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (hEne ρ h0 h1)
      · exact Or.inl
    constructor
    · rintro ⟨hz, h0, h1, hT'⟩; exact ⟨(hstrip h0 h1).mp hz, h0, h1, hT'⟩
    · rintro ⟨hz, h0, h1, hT'⟩; exact ⟨(hstrip h0 h1).mpr hz, h0, h1, hT'⟩
  have hmass : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      mellinMassTerm χ δ ρ = mellinMassTerm ψ δ ρ := by
    intro ρ h0 h1
    simp only [mellinMassTerm, hmult ρ h0 h1]
  have hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im :=
    fun s h0 h1 hτ => corollary_3_2_k0 δ s h0 h1 hτ
  have hψsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction ψ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm ψ δ ρ.val) :=
    tail_mass_summable_of_corollary ψ hψprim δ T hT hcor
  have h₁ : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
        mellinMassTerm ψ δ (Equiv.subtypeEquivRight hzero ρ).val) :=
    (Equiv.summable_iff (Equiv.subtypeEquivRight hzero)).mpr hψsum
  refine h₁.congr (fun ρ => ?_)
  simp only [Equiv.subtypeEquivRight_apply, Subtype.coe_mk]
  exact (hmass ρ.val ρ.property.2.1 ρ.property.2.2.1).symm

/-- LEAF. Pairing inequality. The two sided multiplicity weighted Mellin mass sum is at
most 4.226 times the one sided envelope sum over zeros with positive imaginary part.
The proof splits the two sided sum into positive and negative imaginary parts, maps the
negative part to the positive part by complex conjugation, and applies the pointwise
mass bound. -/
theorem leaf_pairing_inequality (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            (Real.exp (-0.1598 * ρ.val.im) +
              if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) := by
  sorry

/-- Assembly of the split, FREE-nv-glm7 task1604. The statement of `paired_mass_le`
character for character, proved from the three leaves with no gap of its own. -/
theorem paired_mass_le_F1604 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            (Real.exp (-0.1598 * ρ.val.im) +
              if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) := by
  exact ⟨leaf_two_sided_summable q χ δ T hT, leaf_pairing_inequality q χ δ T hT⟩

end DecompF1604

end LeanLab.HelfgottMajor.SplitGaussian123
