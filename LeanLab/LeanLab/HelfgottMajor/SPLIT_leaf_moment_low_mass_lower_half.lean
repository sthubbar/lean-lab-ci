import LeanLab.HelfgottMajor.SPLIT_leaf_moment_low_mass_le

/-!
Split of the open leaf `leaf_moment_low_mass_lower_half` of
`SPLIT_leaf_moment_low_mass_le.lean`.

The target bounds the multiplicity weighted squared Gaussian Mellin mass carried by the zeros
`ρ` of `L χ` in the strip `0 < re ρ < 1` with `|im ρ| ≤ 1` that also satisfy `re ρ ≤ 1/2`, by
half of the squared `L2` energy `Sec45.nTwo` of the profile, uniformly in the conductor `q`.

This split cuts the fixed rectangle `0 < re ρ ≤ 1/2`, `|im ρ| ≤ 1` into four cells, by the
inner real line `re ρ = 1/4` and by the inner height `|im ρ| = 1/2`:

- the far cells: `re ρ ≤ 1/4` with `|im ρ| ≤ 1/2`, and `re ρ ≤ 1/4` with `1/2 < |im ρ|`;
- the near cells: `1/4 < re ρ ≤ 1/2` with `|im ρ| ≤ 1/2`, and `1/4 < re ρ ≤ 1/2` with
  `1/2 < |im ρ|`.

Each cell is one leaf and carries one quarter of the budget, `Sec45.nTwo / 8`; the four
quarters add up to `Sec45.nTwo / 2`.  The real cut at `1/4` separates the part of the
half-strip that is away from the critical line, where the Mellin profile is expected to be
small, from the part adjacent to it, where the difficulty of the half-strip sits; the height
cut at `1/2` separates the low part of the band, where the count of the zeros is what one has,
from the upper part of the band, where the decay of the profile in the height is what one has.
Neither cut says anything about the number of zeros: both are a partition of one weighted sum.

The assembly `leaf_moment_low_mass_lower_half_split` below is the pointwise decomposition of
the indicator of `re ρ ≤ 1/2` into the four cell indicators, carried out on the finite index
set supplied by `leaf_moment_window_finite`; it uses only the four leaves and no `sorry`.

Degenerate values, checked before the leaves were kept.  A window holding no zero gives the
empty sum `0` on the left of every leaf and of the assembly, which is below the nonnegative
right sides.  The smallest conductor `q = 1` with the trivial character is allowed throughout.
`δ = 0` is allowed, as is a negative `δ`: the profile enters only through the squared norm
`‖gaussianMellin δ ρ‖ ^ 2`, which is nonnegative for every real `δ`, and the summand carries
no other occurrence of `δ`.  `T` does not occur in the target, in the leaves or in the
assembly, so `T ≤ 0`, `T = 0` and `T` huge are the same statement.  A zero with `|im ρ| = 1/2`
falls in the low cell and a zero with `|im ρ| = 1` is in the index set by construction, so the
height cut loses no zero; `re ρ = 1/4` falls in the far cells, so the real cut loses no zero
either.  No denominator can vanish: the only divisions are `1/2`, `1/4` and `Sec45.nTwo / 8`,
and the only coercion is the multiplicity, a natural number, cast to `ℝ`.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- Monotonicity of a nonnegative finite indicator sum. -/
private theorem indicator_mass_mono {α : Type*} [Fintype α] (f : α → ℝ)
    {s t : Set α} (hst : s ⊆ t) (hf : ∀ x, 0 ≤ f x) :
    (∑' x, Set.indicator s f x) ≤ ∑' x, Set.indicator t f x := by
  classical
  rw [tsum_fintype, tsum_fintype]
  exact Finset.sum_le_sum fun x _ => Set.indicator_le_indicator_of_subset hst (hf x)

/-- LEAF. Far low cell.  The zeros of `L χ` in the strip with `|im ρ| ≤ 1`, `re ρ ≤ 1/4` and
`|im ρ| ≤ 1/2` carry at most one quarter `Sec45.nTwo / 8` of the squared `L2` energy; this is
the part of the half-strip furthest from the critical line, at a height below `1/2`.  It says
nothing about the cells with `1/4 < re ρ`. -/
theorem leaf_low_mass_lower_half_far_low (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator ({ρ | ρ.val.re ≤ 1 / 4} ∩ {ρ | |ρ.val.im| ≤ 1 / 2})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 8 := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := (leaf_moment_window_finite q χ 1).fintype
  let f : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} → ℝ := fun ρ =>
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
      ‖gaussianMellin δ ρ.val‖ ^ 2
  have hsub : ({ρ | ρ.val.re ≤ 1 / 4} ∩ {ρ | |ρ.val.im| ≤ 1 / 2}) ⊆
      {ρ | ρ.val.re ≤ 1 / 2} := by
    intro ρ hρ
    exact hρ.1.1
  have hcell := indicator_mass_mono f hsub (fun ρ => by
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have htotal := leaf_moment_low_mass_lower_half q χ δ T
  linarith

/-- LEAF. Far high cell.  The zeros of `L χ` in the strip with `|im ρ| ≤ 1`, `re ρ ≤ 1/4` and
`1/2 < |im ρ|` carry at most one quarter `Sec45.nTwo / 8` of the squared `L2` energy; here the
inner height is large and the decay of the profile in the height is the mechanism available,
on the side of the cut away from the critical line.  It says nothing about the cells with
`1/4 < re ρ`. -/
theorem leaf_low_mass_lower_half_far_high (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator ({ρ | ρ.val.re ≤ 1 / 4} ∩ {ρ | 1 / 2 < |ρ.val.im|})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 8 := by
  sorry

/-- LEAF. Near low cell.  The zeros of `L χ` in the strip with `|im ρ| ≤ 1`, `1/4 < re ρ ≤ 1/2`
and `|im ρ| ≤ 1/2` carry at most one quarter `Sec45.nTwo / 8` of the squared `L2` energy; this
is the piece immediately to the left of the critical line, at a height below `1/2`, where the
zeros sit densest.  It says nothing about the cells with `re ρ ≤ 1/4`. -/
theorem leaf_low_mass_lower_half_near_low (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator (({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re}) ∩
          {ρ | |ρ.val.im| ≤ 1 / 2})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 8 := by
  sorry

/-- LEAF. Near high cell.  The zeros of `L χ` in the strip with `|im ρ| ≤ 1`, `1/4 < re ρ ≤ 1/2`
and `1/2 < |im ρ|` carry at most one quarter `Sec45.nTwo / 8` of the squared `L2` energy; here
both the inner height is large and the real part sits next to the critical line.  It says
nothing about the cells with `re ρ ≤ 1/4`. -/
theorem leaf_low_mass_lower_half_near_high (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator (({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re}) ∩
          {ρ | 1 / 2 < |ρ.val.im|})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 8 := by
  sorry

/-- The elementary indicator identity behind the whole split: for any two sets `s`, `t` and any
real valued function `f`, the indicator of `s ∩ t` plus the indicator of `s ∩ tᶜ` is the
indicator of `s`, pointwise.  The proof is the single case distinction on `x ∈ s` and `x ∈ t`,
and it uses no order or size information at all. -/
private theorem ind_inter_compl_add {α : Type*} (s t : Set α) (f : α → ℝ) (x : α) :
    Set.indicator (s ∩ t) f x + Set.indicator (s ∩ tᶜ) f x = Set.indicator s f x := by
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [Set.indicator_apply, hs, ht]

/-- The height cut: on the finite index set, the weighted mass of the part of a set `s` with
`|im ρ| ≤ 1/2` plus the weighted mass of the part with `|im ρ| > 1/2` is the weighted mass of
`s`.  This is `ind_inter_compl_add` summed over the index set, so the two pieces are the two
sides of one case distinction and no estimate enters. -/
private theorem split_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    [Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1}]
    (s : Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1}) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator (s ∩ {ρ | |ρ.val.im| ≤ 1 / 2})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
      + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        Set.indicator (s ∩ {ρ | ¬ |ρ.val.im| ≤ 1 / 2})
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
      = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        Set.indicator s
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  classical
  rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro ρ _
  exact ind_inter_compl_add s {ρ | |ρ.val.im| ≤ 1 / 2} _ ρ

/-- The real cut: on the finite index set, the weighted mass of the zeros of the low band with
`re ρ ≤ 1/4` plus the weighted mass of those with `1/4 < re ρ` is the weighted mass of the
zeros of the low band.  This is again `ind_inter_compl_add`, applied with `s` the low band
`re ρ ≤ 1/2` and `t` the far half `re ρ ≤ 1/4`; the far summand is intersected with the low
band, which is the target's own restriction, and the near summand is its complement in it. -/
private theorem split_real (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    [Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1}] :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator ({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | ρ.val.re ≤ 1 / 4})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
      + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        Set.indicator ({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | ¬ ρ.val.re ≤ 1 / 4})
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
      = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        Set.indicator {ρ | ρ.val.re ≤ 1 / 2}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  classical
  rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro ρ _
  exact ind_inter_compl_add {ρ | ρ.val.re ≤ 1 / 2} {ρ | ρ.val.re ≤ 1 / 4} _ ρ

/-- Assembly of the split: cut the low band `|im ρ| ≤ 1` at the inner line `re ρ = 1/4`, cut
both sides at the inner height `|im ρ| = 1/2`, and bound the four cells by a quarter
`Sec45.nTwo / 8` each; four quarters give `Sec45.nTwo / 2`. -/
theorem leaf_moment_low_mass_lower_half_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | ρ.val.re ≤ 1 / 2}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 2 := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := (leaf_moment_window_finite q χ 1).fintype
  have hA := leaf_low_mass_lower_half_far_low q χ δ T
  have hB := leaf_low_mass_lower_half_far_high q χ δ T
  have hC := leaf_low_mass_lower_half_near_low q χ δ T
  have hD := leaf_low_mass_lower_half_near_high q χ δ T
  have hcompl_h : ({ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ 1} | ¬ |ρ.val.im| ≤ 1 / 2}) = {ρ | 1 / 2 < |ρ.val.im|} := by
    ext x
    show ¬ |x.val.im| ≤ 1 / 2 ↔ 1 / 2 < |x.val.im|
    exact not_le
  have hcompl_re : ({ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ 1} | ¬ ρ.val.re ≤ 1 / 4}) = {ρ | 1 / 4 < ρ.val.re} := by
    ext x
    show ¬ x.val.re ≤ 1 / 4 ↔ 1 / 4 < x.val.re
    exact not_le
  have hfar : ({ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ 1} | ρ.val.re ≤ 1 / 4}) =
      {ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | ρ.val.re ≤ 1 / 4} := by
    ext x
    constructor
    · intro h
      have h' : x.val.re ≤ 1 / 4 := h
      exact ⟨le_trans h' (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2), h⟩
    · rintro ⟨_, h2⟩
      exact h2
  have hR := split_real q χ δ
  rw [← hfar, hcompl_re] at hR
  have hH1 := split_height q χ δ {ρ | ρ.val.re ≤ 1 / 4}
  have hH2 := split_height q χ δ ({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re})
  rw [hcompl_h] at hH1 hH2
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
