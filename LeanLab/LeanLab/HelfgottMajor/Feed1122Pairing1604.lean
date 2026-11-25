import LeanLab.HelfgottMajor.DecompF1604

/-!
Feed burst 2026-11-22, split of the two open leaves of DecompF1604.lean,
`leaf_pointwise_mass_bound` and `leaf_pairing_inequality`. No existing file is edited.

Source: P0014 Helfgott, Major arcs for Goldbach's problem, Corollary 3.2 on page 10 and the
proof of Lemma 4.5 on pages 40 and 41, displays 4.33 to 4.35.

Route note, recorded in PROGRESS.md 2026-11-12 and 2026-11-13. The printed step before
display 4.33 pairs rho with 1 - rho by the functional equation. That keeps one zero set only
for a real character: for complex chi the zeros of L of s and chi below minus T are 1 - rho
for rho the zeros of L of s and the conjugate character above T. So this split does not use
the printed pairing. It uses instead:

1. a pointwise Gaussian bound with constant 1 in place of 4.226, a sharpening of Corollary 3.2
   that the lab numerics support, a ratio at most 0.93 at the threshold;
2. summability of the two sided envelope sum, from the quadratic shell count already in
   Gaussian123Base;
3. a comparison of the negative half envelope sum with 3.226 times the positive half envelope
   sum, a zero counting step for L of s and chi against L of s and the conjugate character.

The two parent statements are proved here from these leaves, as
`leaf_pointwise_mass_bound_feed1122` and `leaf_pairing_inequality_feed1122`, each with the
statement of its parent character for character. AI wrote this Lean code.
Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122Pairing1604
open Real LeanLab.HelfgottMajor.SplitGaussian123

/-- LEAF: P0014 Theorem 3.1 and Corollary 3.2, pages 9 and 10, display 3.4 with k equal to 0,
sharpened to constant 1. HARD. For s in the closed critical strip with abs Im s at least
max of 100 and 4 pi squared abs delta, the norm of the Mellin transform F_delta of
exp of minus t squared over 2 times e of delta t is at most exp of minus 0.1598 abs Im s plus,
away from zero shift, exp of minus 0.1065 times the square of Im s over pi abs delta.
A statement about the Gaussian alone. Corollary 3.2 gives this with the factor 4.226 for the
sum of F_delta at s and at 1 - s; the lab mpmath check of 2026-11-13, PROGRESS.md, gives
ratio at most 0.22 of that bound at the threshold, so the constant 1 form looks true. -/
theorem leaf_gaussian_mellin_norm_le (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ ≤
      Real.exp (-0.1598 * |s.im|) +
        if δ = 0 then 0 else Real.exp (-0.1065 * (s.im / (π * |δ|)) ^ 2) := by
  sorry

/-- Assembled from `leaf_gaussian_mellin_norm_le`. The statement of
`DecompF1604.leaf_pointwise_mass_bound` character for character. -/
theorem leaf_pointwise_mass_bound_feed1122 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}) :
    mellinMassTerm χ δ ρ.val ≤
      (ZeroCount1623.mult χ ρ.val : ℝ) *
        (Real.exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) := by
  have hT' : max 100 (4 * π ^ 2 * |δ|) ≤ |ρ.val.im| := by
    rw [max_comm]; exact hT.trans ρ.property.2.2.2.le
  have hn := leaf_gaussian_mellin_norm_le δ ρ.val ρ.property.2.1.le ρ.property.2.2.1.le hT'
  unfold mellinMassTerm
  exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)

/-- Norm of a Dirichlet character value at a unit is one: the value is a root of unity. -/
private lemma feed_norm_apply_unit {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
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
private lemma feed_euler_factor_ne_zero {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
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
      simpa only [hu.unit_spec] using feed_norm_apply_unit ψ hu.unit
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
private lemma feed_euler_prod_ne_zero {M q : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    (∏ p ∈ q.primeFactors, (1 - ψ (p : ZMod M) * (p : ℂ) ^ (-s))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact feed_euler_factor_ne_zero ψ p (Nat.mem_primeFactors.mp hp).1 s h0 h1

/-- The finite Euler product of the induced level is analytic. -/
private lemma feed_analyticAt_euler_prod {M q : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (s : ℂ) :
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

/-- LEAF: P0014 Lemma 4.5 page 41 with Lemma 4.3 pages 37 and 38, summability of the two
sided envelope sum. MEDIUM. Over the strip zeros of L of s and chi above height T in absolute
value, the multiplicity times the two branch envelope is summable. Route: reduce to the
primitive character inducing chi as in `DecompF1604.leaf_two_sided_summable`, then apply
`tail_envelope_summable_of_shell_count` with `tail_shell_count_le_quadratic` of
Gaussian123Base; the Gaussian branch there is written with abs Im, equal after squaring. -/
theorem leaf_two_sided_envelope_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
        (ZeroCount1623.mult χ ρ.val : ℝ) *
          (Real.exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) := by
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
    intro z; rw [hEdef]; exact feed_analyticAt_euler_prod ψ z
  have hEne : ∀ z : ℂ, 0 < z.re → z.re < 1 → E z ≠ 0 := by
    intro z h0 h1; rw [hEdef]; exact feed_euler_prod_ne_zero ψ z h0 h1
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
  have hT1 : 1 ≤ T := by have := (le_max_right _ _).trans hT; linarith
  have hψsum := tail_envelope_summable_of_shell_count ψ δ T (2 * (χ.conductor : ℝ) + 18) hT1
    (tail_shell_count_le_quadratic ψ hψprim T)
  have h₁ := (Equiv.summable_iff (Equiv.subtypeEquivRight hzero)).mpr hψsum
  refine h₁.congr (fun ρ => ?_)
  rw [hmult ρ.val ρ.property.2.1 ρ.property.2.2.1]
  simp only [Function.comp_apply, Equiv.subtypeEquivRight_apply, div_pow, sq_abs]


/-- LEAF: P0014 Lemma 4.5 page 41, displays 4.33 to 4.35, the half plane comparison that
replaces the printed pairing of rho with 1 - rho. HARD. The envelope sum over the strip zeros
of L of s and chi with negative imaginary part below minus T is at most 3.226 times the
envelope sum over those with positive imaginary part above T. By conjugation and
`ZeroCount1623.mult_inv_conj` the left side is the positive half envelope sum of the
conjugate character, so this compares the zero counts of L of s and chi and of L of s and
the conjugate character against a decreasing weight, by Lemma 4.3. For a real character
the two sides are equal and the bound is trivial. Also asserts summability of the negative
half. -/
theorem leaf_negative_half_envelope_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im < 0 ∧ T < |ρ.im|},
        (ZeroCount1623.mult χ ρ.val : ℝ) *
          (Real.exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) ≤
      3.226 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            (Real.exp (-0.1598 * ρ.val.im) +
              if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) := by
  sorry

/-- Assembled. The statement of `DecompF1604.leaf_pairing_inequality` character for
character, from the pointwise bound, the two sided envelope summability and the half plane
comparison, by splitting the two sided envelope sum by the sign of the imaginary part. -/
theorem leaf_pairing_inequality_feed1122 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) *
            (Real.exp (-0.1598 * ρ.val.im) +
              if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2))) := by
  classical
  have hT0 : 0 < T := by have := (le_max_right _ _).trans hT; linarith
  set I := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} with hI
  set J := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} with hJ
  set N := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im < 0 ∧ T < |ρ.im|} with hN
  set g : ℂ → ℝ := fun z => (ZeroCount1623.mult χ z : ℝ) *
      (Real.exp (-0.1598 * |z.im|) +
        if δ = 0 then 0 else Real.exp (-0.1065 * (z.im / (π * |δ|)) ^ 2)) with hg
  have hgsum : Summable (fun ρ : I => g ρ.val) :=
    leaf_two_sided_envelope_summable q χ δ T hT
  have hmsum : Summable (fun ρ : I => mellinMassTerm χ δ ρ.val) :=
    leaf_two_sided_summable q χ δ T hT
  have h1 : (∑' ρ : I, mellinMassTerm χ δ ρ.val) ≤ ∑' ρ : I, g ρ.val :=
    hmsum.tsum_le_tsum (fun ρ => leaf_pointwise_mass_bound_feed1122 q χ δ T hT ρ) hgsum
  have hsplit := hgsum.tsum_subtype_add_tsum_subtype_compl {x : I | 0 < x.val.im}
  let eP : {x : I // x ∈ {x : I | 0 < x.val.im}} ≃ J :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.2, by
          have h := x.1.2.2.2.2; have hx : 0 < x.1.1.im := x.2
          rwa [abs_of_pos hx] at h⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1, by
          rw [abs_of_pos y.2.2.2.2.1]; exact y.2.2.2.2.2⟩, y.2.2.2.2.1⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let eN : {x : I // x ∈ ({x : I | 0 < x.val.im}ᶜ)} ≃ N :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, by
          have h := x.1.2.2.2.2
          have hx : ¬ 0 < x.1.1.im := x.2
          have hne : x.1.1.im ≠ 0 := by
            intro h0; rw [h0, abs_zero] at h; linarith
          exact lt_of_le_of_ne (not_lt.mp hx) hne, x.1.2.2.2.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.2⟩, by
          show ¬ 0 < y.1.im
          exact not_lt.mpr y.2.2.2.2.1.le⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hP : (∑' x : {x : I // x ∈ {x : I | 0 < x.val.im}}, g x.val.val) =
      ∑' ρ : J, (ZeroCount1623.mult χ ρ.val : ℝ) *
        (Real.exp (-0.1598 * ρ.val.im) +
          if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) := by
    rw [← eP.symm.tsum_eq]
    apply tsum_congr
    intro y
    have hy : 0 < y.val.im := y.2.2.2.2.1
    simp only [hg, eP, Equiv.coe_fn_symm_mk, abs_of_pos hy]
  have hNeq : (∑' x : {x : I // x ∈ ({x : I | 0 < x.val.im}ᶜ)}, g x.val.val) =
      ∑' ρ : N, g ρ.val := by
    rw [← eN.symm.tsum_eq]
    rfl
  have h2 := leaf_negative_half_envelope_le q χ δ T hT
  have h3 : (∑' ρ : I, g ρ.val) ≤ 4.226 * ∑' ρ : J, (ZeroCount1623.mult χ ρ.val : ℝ) *
        (Real.exp (-0.1598 * ρ.val.im) +
          if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) := by
    rw [← hsplit, hP, hNeq]
    have h2' : (∑' ρ : N, g ρ.val) ≤ 3.226 * ∑' ρ : J, (ZeroCount1623.mult χ ρ.val : ℝ) *
        (Real.exp (-0.1598 * ρ.val.im) +
          if δ = 0 then 0 else Real.exp (-0.1065 * (ρ.val.im / (π * |δ|)) ^ 2)) := h2
    linarith
  exact h1.trans h3

end LeanLab.HelfgottMajor.Feed1122Pairing1604

