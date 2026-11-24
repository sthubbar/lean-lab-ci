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
  sorry

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

