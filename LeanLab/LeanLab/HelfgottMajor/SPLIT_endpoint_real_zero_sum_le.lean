import LeanLab.task783.RealZeroSum

/-!
# Split of `endpoint_real_zero_sum_le` (`HelfgottMajor/SPLIT_endpoint_strip_sum_le`)

The target says: for a primitive character `χ` of conductor `q ≥ 2π`, the strip zeros of
`L(s, χ)` on the real axis below height `2π/q` carry at most one unit of multiplicity.

The split is exact.  By the functional equation pairing `β ↦ 1 - β` of real zeros, Davenport
chapter 9, proved in `LeanLab.task783.RealZeroPairs`, the target is equivalent to the two named
statements below, and both directions are proved:

* `real_strip_zero_eq_half`: every real zero `β ∈ (0, 1)` of `L(s, χ)` is `1/2`.  This contains
  the nonexistence of a Landau Siegel zero for every primitive `χ` with `q ≥ 2π`, an open problem;
* `half_zero_mult_le_one`: `L(s, χ)` vanishes at most to order one at `1/2`, a Chowla type
  statement, also open.

`endpoint_real_zero_sum_le_split` proves the target statement from the two leaves, and
`endpoint_real_zero_leaves_of_sum_le` proves the two leaves from the target statement, through
`LeanLab.task783.RealZeroSum`.  So neither leaf is stronger than the target, and the target is
no weaker than the Landau Siegel problem.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitEndpointRealZero

open Real

variable {q : ℕ} [NeZero q]

/-- LEAF: real zeros of a primitive `L(s, χ)` lie at `1/2`; the absence of real zeros off the
critical line, which for real `χ` is the absence of a Landau Siegel zero, Davenport chapter 14,
an open problem for general `q`; verified only for finitely many moduli, for instance by
Platt's computations.  HARD. -/
theorem real_strip_zero_eq_half (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 2 * π ≤ (q : ℝ)) {β : ℝ} (h0 : 0 < β) (h1 : β < 1)
    (hz : DirichletCharacter.LFunction χ β = 0) : β = 1 / 2 := by
  sorry

/-- LEAF: the order of vanishing of a primitive `L(s, χ)` at the central point `1/2` is at most
one; for real `χ` Chowla's conjecture says it is zero, open in general.  HARD. -/
theorem half_zero_mult_le_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 2 * π ≤ (q : ℝ)) :
    LeanLab.HelfgottMajor.ZeroCount1623.mult χ (1 / 2) ≤ 1 := by
  sorry

/-- The two real zero statements give the bound of the target, at any height: the real strip
zeros are then at most the single point `1/2`, of weight at most one. -/
theorem real_zero_sum_le_of_leaves (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hhalf : ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ β = 0 → β = 1 / 2)
    (hmult : LeanLab.HelfgottMajor.ZeroCount1623.mult χ (1 / 2) ≤ 1) :
    (∑ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T).toFinset.filter
        (fun ρ => ρ.im = 0), (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ)) ≤ 1 := by
  have hsub : (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T).toFinset.filter
      (fun ρ => ρ.im = 0) ⊆ ({(1 / 2 : ℂ)} : Finset ℂ) := by
    intro ρ hρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset,
      LeanLab.HelfgottMajor.ZeroCount1623.stripZeros, Set.mem_setOf_eq] at hρ
    obtain ⟨⟨hz, h0, h1, _⟩, him⟩ := hρ
    have hρeq : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hz' : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by rw [← hρeq]; exact hz
    have hb := hhalf ρ.re h0 h1 hz'
    rw [Finset.mem_singleton, hρeq, hb]
    push_cast
    ring
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun ρ => (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ))
    (fun _ _ _ => Nat.cast_nonneg _)
  rw [Finset.sum_singleton] at hle
  have : (LeanLab.HelfgottMajor.ZeroCount1623.mult χ (1 / 2) : ℝ) ≤ 1 := by exact_mod_cast hmult
  linarith

/-- The target `Decomp388a.endpoint_real_zero_sum_le`, verbatim, from the two leaves. -/
theorem endpoint_real_zero_sum_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    (∑ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => ρ.im = 0), (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ)) ≤ 1 :=
  real_zero_sum_le_of_leaves χ _ (fun _ h0 h1 hz => real_strip_zero_eq_half χ hχ hq h0 h1 hz)
    (half_zero_mult_le_one χ hχ hq)

/-- The converse: the target statement, taken as the hypothesis `hsum`, gives both leaf
statements, by `LeanLab.task783.RealZeroSum`.  So the split loses nothing. -/
theorem endpoint_real_zero_leaves_of_sum_le (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 2 * π ≤ (q : ℝ))
    (hsum : (∑ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
        (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0),
        (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ)) ≤ 1) :
    (∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ β = 0 → β = 1 / 2) ∧
      LeanLab.HelfgottMajor.ZeroCount1623.mult χ (1 / 2) ≤ 1 := by
  refine ⟨fun β h0 h1 hz =>
    LeanLab.task783.RealZeroSum.real_zero_eq_half_of_sum_le_one χ hχ hq hsum h0 h1 hz, ?_⟩
  by_cases hz : DirichletCharacter.LFunction χ (1 / 2) = 0
  · exact LeanLab.task783.RealZeroSum.half_zero_simple_of_sum_le_one χ hsum hz
  · have h0 : LeanLab.HelfgottMajor.ZeroCount1623.mult χ (1 / 2) = 0 := by
      unfold LeanLab.HelfgottMajor.ZeroCount1623.mult
      have h := analyticOrderAt_eq_zero.mpr (Or.inr hz)
      simp only [analyticOrderNatAt, h, ENat.toNat_zero]
    omega

end LeanLab.HelfgottMajor.SplitEndpointRealZero
