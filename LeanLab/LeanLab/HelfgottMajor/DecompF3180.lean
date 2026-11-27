import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_one
import LeanLab.HelfgottMajor.Conductor669

/-!
# Split of the conductors `13` to `17` band multiplicity bound

FREE-nv-nemotron task3180. This file imports the target module and does not edit it.
The target bounds the multiplicity of every strip zero in the short window
`(1, 2πe / q]` for a primitive character whose conductor is between `13` and `17`.
The finite conductor range reduces the target to five cases.

The modulus `14` case is vacuous because no primitive character has modulus `14`.
The other four cases fix the modulus at `13`, `15`, `16`, or `17`. Each is one
multiplicity estimate in a fixed low conductor case and is strictly easier than the
range statement. The assembly has the target statement character for character and
is proved from the five case leaves with no gap of its own.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-! The window height `2πe / q` is above `1` for every conductor in `13` to `17`, so
the filter `1 < ρ.im` defines a non-trivial interval rather than an empty one. This is a
purely numerical fact about the band height; it says nothing about whether any zeros lie in
the interval. Proved, no input. -/
lemma band_height_gt_one {q : ℕ} [NeZero q] (hq13 : q ≥ 13) (hq17 : q ≤ 17) :
    1 < 2 * Real.pi * Real.exp 1 / (q : ℝ) := by
  have h : (2 : ℝ) * Real.pi * Real.exp 1 / (q : ℝ) ≥ (2 : ℝ) * Real.pi * Real.exp 1 / 17 := by
    apply div_le_div_of_le_left (by positivity) (by linarith)
    nlinarith [Real.pi_pos, Real.exp_pos 1]
  have h2 : (2 : ℝ) * Real.pi * Real.exp 1 / 17 > 1 := by
    have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
    have hexp : (2.718281828 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h : (2 : ℝ) * Real.pi * Real.exp 1 > (2 : ℝ) * 3.1415 * 2.718281828 := by
      nlinarith
    norm_num at h ⊢
    <;> linarith
  linarith

/-- LEAF. Conductor `13` fixes the modulus in the short band window. Every strip zero of
`L(·, χ)` with imaginary part in `(1, 2πe / 13]` has multiplicity at most one. -/
theorem band_above_one_mult_level_thirteen_F3180
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 13) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- No character of modulus `14` is primitive, because every such character factors through
modulus `7`. This closes the empty modulus `14` case without creating a leaf with impossible
hypotheses. -/
private lemma no_primitive_fourteen_F3180 (χ : DirichletCharacter ℂ q) (hq : q = 14) :
    ¬ χ.IsPrimitive := by
  subst hq
  exact LeanLab.HelfgottMajor.Conductor669.not_primitive_fourteen χ

/-- LEAF. Conductor `15` fixes the modulus in the short band window. Every strip zero of
`L(·, χ)` with imaginary part in `(1, 2πe / 15]` has multiplicity at most one. -/
theorem band_above_one_mult_level_fifteen_F3180
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 15) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF. Conductor `16` fixes the modulus in the short band window. Every strip zero of
`L(·, χ)` with imaginary part in `(1, 2πe / 16]` has multiplicity at most one. -/
theorem band_above_one_mult_level_sixteen_F3180
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 16) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF. Conductor `17` fixes the modulus in the short band window. Every strip zero of
`L(·, χ)` with imaginary part in `(1, 2πe / 17]` has multiplicity at most one. -/
theorem band_above_one_mult_level_seventeen_F3180
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 17) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Assembly of the conductors `13` to `17` band multiplicity bound. The integer interval
has only five possible conductors, and the corresponding fixed-conductor leaves give the
desired estimate in each case. -/
theorem book_count_band_above_one_mult_le_one_level_le_seventeen_F3180
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq13 : 13 ≤ q) (hq17 : q ≤ 17) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  have hcases : q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by omega
  rcases hcases with h | h | h | h | h
  · subst h
    exact band_above_one_mult_level_thirteen_F3180 χ hχ rfl
  · subst h
    exact absurd hχ (no_primitive_fourteen_F3180 χ rfl)
  · subst h
    exact band_above_one_mult_level_fifteen_F3180 χ hχ rfl
  · subst h
    exact band_above_one_mult_level_sixteen_F3180 χ hχ rfl
  · subst h
    exact band_above_one_mult_level_seventeen_F3180 χ hχ rfl

#print axioms book_count_band_above_one_mult_le_one_level_le_seventeen_F3180

end LeanLab.HelfgottMajor.ZeroCount1623
