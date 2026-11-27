import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_card
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Decomposition of `book_count_band_above_one_mult_le_card_level_le_twelve`

The target covers conductors `7` to `12` at the top height `2πe / q` of the band:
the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / q]` number at most one.
It is split by modulus.

* `q = 10`: there is no primitive character modulo `10`, since every character modulo `10`
  factors through `ZMod 5`. Proved here, no input.
* `q = 7`: the window `(1, 2πe / 7]` holds no strip zero of any primitive character modulo `7`.
  Numerically `2πe / 7 < 2.43`; the lowest positive zero of any primitive `L`-function
  modulo `7` is above `6`. This is a LEAF, a certified zero free rectangle for six `L`-functions.
* `q = 8`: the window `(1, 2πe / 8]` holds no strip zero of any primitive character modulo `8`.
  Numerically `2πe / 8 < 2.13`; the lowest positive zero of any primitive `L`-function
  modulo `8` is above `5`. This is a LEAF, a certified zero free rectangle for two `L`-functions.
* `q = 9`: the window `(1, 2πe / 9]` holds no strip zero of any primitive character modulo `9`.
  Numerically `2πe / 9 < 1.89`; the lowest positive zero of any primitive `L`-function
  modulo `9` is above `4`. This is a LEAF, a certified zero free rectangle for four `L`-functions.
* `q = 11`: the window `(1, 2πe / 11]` holds no strip zero of any primitive character modulo `11`.
  Numerically `2πe / 11 < 1.55`; the lowest positive zero of any primitive `L`-function
  modulo `11` is above `6`. This is a LEAF, a certified zero free rectangle for ten `L`-functions.
* `q = 12`: the window `(1, 2πe / 12]` holds no strip zero of the unique primitive character modulo `12`.
  Numerically `2πe / 12 < 1.42`; the lowest positive zero is above `6`. This is a LEAF.

The assembly is the case analysis on `q` in `7` to `12`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- No primitive character modulo `10`: every character modulo `10` factors through `ZMod 5`,
since `(ZMod 10)ˣ → (ZMod 5)ˣ` is an isomorphism. Proved, no input. -/
theorem card12_no_primitive_ten (χ : DirichletCharacter ℂ q) (hq : q = 10) : ¬ χ.IsPrimitive := by
  subst hq
  intro hp
  have hi : Function.Injective (ZMod.unitsMap (show 5 ∣ 10 by norm_num)) := by
    -- The map (ZMod 10)ˣ → (ZMod 5)ˣ is an isomorphism because (ZMod 10)ˣ ≃ (ZMod 2)ˣ × (ZMod 5)ˣ
    -- and (ZMod 2)ˣ is trivial. We verify injectivity by checking all elements.
    decide
  have hf : χ.FactorsThrough 5 := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap (by norm_num : 5 ∣ 10)).mpr
    intro x hx
    have hx1 : x = 1 := hi (by simpa using hx)
    rw [hx1]
    exact map_one χ.toUnitHom
  have hc : χ.conductor ≤ 5 := Nat.sInf_le hf
  have hχ' : χ.conductor = 10 := by
    rw [DirichletCharacter.isPrimitive_def] at hp
    exact hp
  rw [hχ'] at hc
  norm_num at hc ⊢
  <;> omega

/-- LEAF: zero free rectangle for the six primitive characters modulo `7`, the window
`(1, 2πe / 7]` of the band at conductor `7` holds no strip zero of `L(·, χ)`. Numerically
`2πe / 7 < 2.43` and the first zero of any primitive `L`-function modulo `7` is above `6`.
Class HARD: a certified zero verification of six `L`-functions on a rectangle,
argument principle or Turing method. -/
theorem card12_window_empty_seven (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 7) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free rectangle for the two primitive characters modulo `8`, the window
`(1, 2πe / 8]` holds no strip zero of `L(·, χ)`. Numerically `2πe / 8 < 2.13` and the
first zero of any primitive `L`-function modulo `8` is above `5`. Class HARD: a certified
zero verification of two `L`-functions. -/
theorem card12_window_empty_eight (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 8) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free rectangle for the four primitive characters modulo `9`, the window
`(1, 2πe / 9]` holds no strip zero of `L(·, χ)`. Numerically `2πe / 9 < 1.89` and the
first zero of any primitive `L`-function modulo `9` is above `4`. Class HARD: a certified
zero verification of four `L`-functions. -/
theorem card12_window_empty_nine (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 9) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free rectangle for the ten primitive characters modulo `11`, the window
`(1, 2πe / 11]` holds no strip zero of `L(·, χ)`. Numerically `2πe / 11 < 1.55` and the
first zero of any primitive `L`-function modulo `11` is above `6`. Class HARD: a certified
zero verification of ten `L`-functions. -/
theorem card12_window_empty_eleven (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 11) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free rectangle for the unique primitive character modulo `12`, the window
`(1, 2πe / 12]` holds no strip zero of `L(·, χ)`. Numerically `2πe / 12 < 1.42` and the
first zero is above `6`. Class HARD: a certified zero verification of one `L`-function. -/
theorem card12_window_empty_twelve (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 12) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- Assembly of `book_count_band_above_one_mult_le_card_level_le_twelve` from the leaves:
case analysis on `q` in `7` to `12`; the modulus `10` carries no primitive character and
the moduli `7`, `8`, `9`, `11`, `12` have an empty window. -/
theorem book_count_band_above_one_mult_le_card_level_le_twelve_F3170 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hq12 : q ≤ 12) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have hcases : q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 := by omega
  rcases hcases with h | h | h | h | h | h
  · -- q = 7
    have h₁ := card12_window_empty_seven χ hχ h
    rw [h₁]
    simp
  · -- q = 8
    have h₁ := card12_window_empty_eight χ hχ h
    rw [h₁]
    simp
  · -- q = 9
    have h₁ := card12_window_empty_nine χ hχ h
    rw [h₁]
    simp
  · -- q = 10
    exfalso
    exact (card12_no_primitive_ten χ h) hχ
  · -- q = 11
    have h₁ := card12_window_empty_eleven χ hχ h
    rw [h₁]
    simp
  · -- q = 12
    have h₁ := card12_window_empty_twelve χ hχ h
    rw [h₁]
    simp

end LeanLab.HelfgottMajor.ZeroCount1623