import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of the isolation leaves at conductors `13` and `17`, burst 20261127 S2

The burst S2 split files `SPLIT_veryLow_level_thirteen_sum_le_one` and
`SPLIT_veryLow_level_seventeen_sum_le_one` each carry an isolation LEAF,
`thirteen_low_zero_unique` and `seventeen_low_zero_unique`: for `χ` primitive modulo `13`,
respectively `17`, two zeros of `L(s, χ)` within `1/100` of `c = 1/2 + 0.88396 i`, respectively
`c = 1/2 + 0.39131 i`, are equal. This is the isolation part of Platt's verification [Pla11],
cited in Helfgott arXiv 1305.2897v4 Section 4.6 page 56.

Here the isolation is certified by a derivative enclosure on the disk, the standard Newton or
Krawczyk style test: if `|L'(c)| ≥ 1/2` and `|L'(s) - L'(c)| ≤ 1/10` on the disk, then
`s ↦ L(s) - L'(c) s` is `1/10` Lipschitz there by the mean value inequality, so `L` is injective
on the disk. That passage is PROVED here, `eq_of_zero_of_deriv_close`. What remains is two LEAF
lemmas per conductor, each assuming the disk holds a zero: the lower bound at the centre and the
oscillation bound. Numerically, burst 20261127 S2 with mpmath, for the one character with a zero
in the disk, `|L'(c)| ≈ 0.877` and `max |L'(s) - L'(c)| ≈ 0.0095` on the boundary circle at
conductor `13`, and `0.837` and `0.0059` at conductor `17`; by the maximum principle the
boundary maximum bounds the disk.

The twins `thirteen_low_zero_unique_of_leaves` and `seventeen_low_zero_unique_of_leaves` have
exactly the statements of the two isolation leaves. AI wrote this Lean code. Binary Goldbach is
open.
-/

namespace LeanLab.HelfgottMajor.SPLIT_low_zero_unique_thirteen_seventeen
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- Mean value step: if `f` is differentiable on the open disk `‖s - c‖ < r` and
`‖f'(s) - f'(c)‖ ≤ M < ‖f'(c)‖` there, then two zeros of `f` in the disk are equal. Proved. -/
theorem eq_of_zero_of_deriv_close (f : ℂ → ℂ) (c : ℂ) {r M : ℝ}
    (hf : ∀ s, ‖s - c‖ < r → DifferentiableAt ℂ f s)
    (hosc : ∀ s, ‖s - c‖ < r → ‖deriv f s - deriv f c‖ ≤ M) (hM : M < ‖deriv f c‖)
    (ρ₁ ρ₂ : ℂ) (h₁ : ‖ρ₁ - c‖ < r) (h₂ : ‖ρ₂ - c‖ < r) (hz₁ : f ρ₁ = 0) (hz₂ : f ρ₂ = 0) :
    ρ₁ = ρ₂ := by
  set a := deriv f c
  set S : Set ℂ := Metric.ball c r
  have hS : Convex ℝ S := convex_ball c r
  have hmemS : ∀ s, s ∈ S ↔ ‖s - c‖ < r := fun s => by
    simp [S, Metric.mem_ball, dist_eq_norm]
  have hg : ∀ s ∈ S, HasDerivWithinAt (fun z => f z - a * z) (deriv f s - a * 1) S s := by
    intro s hs
    exact (((hf s ((hmemS s).mp hs)).hasDerivAt).sub
      ((hasDerivAt_id s).const_mul a)).hasDerivWithinAt
  have hb : ∀ s ∈ S, ‖deriv f s - a * 1‖ ≤ M := by
    intro s hs
    rw [mul_one]
    exact hosc s ((hmemS s).mp hs)
  have key := hS.norm_image_sub_le_of_norm_hasDerivWithin_le hg hb
    ((hmemS ρ₁).mpr h₁) ((hmemS ρ₂).mpr h₂)
  have hcalc : (f ρ₂ - a * ρ₂) - (f ρ₁ - a * ρ₁) = -(a * (ρ₂ - ρ₁)) := by
    rw [hz₁, hz₂]; ring
  rw [hcalc, norm_neg, norm_mul] at key
  by_contra hne
  have hpos : 0 < ‖ρ₂ - ρ₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have := le_of_mul_le_mul_right key hpos
  linarith

/-- A point within `1/100` of a point of real part `1/2` is not `1`. -/
theorem ne_one_of_near_half {s c : ℂ} (hc : c.re = 1 / 2) (hd : ‖s - c‖ < 1 / 100) : s ≠ 1 := by
  rintro rfl
  have h := (Complex.abs_re_le_norm (1 - c)).trans_lt hd
  rw [sub_re, one_re, hc, abs_of_pos (by norm_num)] at h
  norm_num at h

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
isolation step for conductor `13`, centre bound: for `χ` primitive modulo `13` such that
`L(s, χ)` has a zero within `1/100` of `c = 1/2 + 0.88396 i`, `|L'(c, χ)| ≥ 1/2`. Numerically
only the character with `χ(2) = exp(5πi/6)` has such a zero, and `|L'(c, χ)| ≈ 0.877`.
Class MEDIUM: a certified evaluation of `L'` at one point. -/
theorem thirteen_deriv_centre_ge (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) (ρ₀ : ℂ) (hL : DirichletCharacter.LFunction χ ρ₀ = 0)
    (hd : ‖ρ₀ - ⟨1 / 2, 88396 / 100000⟩‖ < 1 / 100) :
    1 / 2 ≤ ‖deriv (DirichletCharacter.LFunction χ) ⟨1 / 2, 88396 / 100000⟩‖ := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
isolation step for conductor `13`, oscillation bound: for `χ` primitive modulo `13` such that
`L(s, χ)` has a zero within `1/100` of `c = 1/2 + 0.88396 i`, `|L'(s, χ) - L'(c, χ)| ≤ 1/10`
for every `s` within `1/100` of `c`. Numerically the maximum on the boundary circle is
`≈ 0.0095`. Class MEDIUM: a certified bound for `L''` on a small disk. -/
theorem thirteen_deriv_osc_le (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) (ρ₀ : ℂ) (hL : DirichletCharacter.LFunction χ ρ₀ = 0)
    (hd : ‖ρ₀ - ⟨1 / 2, 88396 / 100000⟩‖ < 1 / 100) (s : ℂ)
    (hs : ‖s - ⟨1 / 2, 88396 / 100000⟩‖ < 1 / 100) :
    ‖deriv (DirichletCharacter.LFunction χ) s -
      deriv (DirichletCharacter.LFunction χ) ⟨1 / 2, 88396 / 100000⟩‖ ≤ 1 / 10 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
isolation step for conductor `17`, centre bound: for `χ` primitive modulo `17` such that
`L(s, χ)` has a zero within `1/100` of `c = 1/2 + 0.39131 i`, `|L'(c, χ)| ≥ 1/2`. Numerically
only the character with `χ(3) = exp(-5πi/8)` has such a zero, and `|L'(c, χ)| ≈ 0.837`.
Class MEDIUM: a certified evaluation of `L'` at one point. -/
theorem seventeen_deriv_centre_ge (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ₀ : ℂ) (hL : DirichletCharacter.LFunction χ ρ₀ = 0)
    (hd : ‖ρ₀ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100) :
    1 / 2 ≤ ‖deriv (DirichletCharacter.LFunction χ) ⟨1 / 2, 39131 / 100000⟩‖ := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
isolation step for conductor `17`, oscillation bound: for `χ` primitive modulo `17` such that
`L(s, χ)` has a zero within `1/100` of `c = 1/2 + 0.39131 i`, `|L'(s, χ) - L'(c, χ)| ≤ 1/10`
for every `s` within `1/100` of `c`. Numerically the maximum on the boundary circle is
`≈ 0.0059`. Class MEDIUM: a certified bound for `L''` on a small disk. -/
theorem seventeen_deriv_osc_le (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ₀ : ℂ) (hL : DirichletCharacter.LFunction χ ρ₀ = 0)
    (hd : ‖ρ₀ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100) (s : ℂ)
    (hs : ‖s - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100) :
    ‖deriv (DirichletCharacter.LFunction χ) s -
      deriv (DirichletCharacter.LFunction χ) ⟨1 / 2, 39131 / 100000⟩‖ ≤ 1 / 10 := by
  sorry

/-- Twin of `SPLIT_veryLow_level_thirteen_sum_le_one.thirteen_low_zero_unique`, exactly its
statement, from the two conductor `13` leaves and `eq_of_zero_of_deriv_close`. -/
theorem thirteen_low_zero_unique_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) (ρ₁ ρ₂ : ℂ) (hL₁ : DirichletCharacter.LFunction χ ρ₁ = 0)
    (hL₂ : DirichletCharacter.LFunction χ ρ₂ = 0)
    (hd₁ : ‖ρ₁ - ⟨1 / 2, 88396 / 100000⟩‖ < 1 / 100)
    (hd₂ : ‖ρ₂ - ⟨1 / 2, 88396 / 100000⟩‖ < 1 / 100) : ρ₁ = ρ₂ :=
  eq_of_zero_of_deriv_close (DirichletCharacter.LFunction χ) ⟨1 / 2, 88396 / 100000⟩
    (fun s hs => DirichletCharacter.differentiableAt_LFunction χ s
      (Or.inl (ne_one_of_near_half rfl hs)))
    (thirteen_deriv_osc_le χ hχ hq ρ₁ hL₁ hd₁)
    (by have := thirteen_deriv_centre_ge χ hχ hq ρ₁ hL₁ hd₁; linarith)
    ρ₁ ρ₂ hd₁ hd₂ hL₁ hL₂

/-- Twin of `SPLIT_veryLow_level_seventeen_sum_le_one.seventeen_low_zero_unique`, exactly its
statement, from the two conductor `17` leaves and `eq_of_zero_of_deriv_close`. -/
theorem seventeen_low_zero_unique_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ₁ ρ₂ : ℂ) (hL₁ : DirichletCharacter.LFunction χ ρ₁ = 0)
    (hL₂ : DirichletCharacter.LFunction χ ρ₂ = 0)
    (hd₁ : ‖ρ₁ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100)
    (hd₂ : ‖ρ₂ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100) : ρ₁ = ρ₂ :=
  eq_of_zero_of_deriv_close (DirichletCharacter.LFunction χ) ⟨1 / 2, 39131 / 100000⟩
    (fun s hs => DirichletCharacter.differentiableAt_LFunction χ s
      (Or.inl (ne_one_of_near_half rfl hs)))
    (seventeen_deriv_osc_le χ hχ hq ρ₁ hL₁ hd₁)
    (by have := seventeen_deriv_centre_ge χ hχ hq ρ₁ hL₁ hd₁; linarith)
    ρ₁ ρ₂ hd₁ hd₂ hL₁ hL₂

end LeanLab.HelfgottMajor.SPLIT_low_zero_unique_thirteen_seventeen
