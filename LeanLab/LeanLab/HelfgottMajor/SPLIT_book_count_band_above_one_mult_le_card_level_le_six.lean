import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le

/-!
# Split of `book_count_band_above_one_mult_le_card_level_le_six`

The parent block covers the conductors `2` to `6` at the top height `2πe / q` of the band:
the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / q]` number at most one. It is split by modulus.

* `q = 2`: there is no primitive character modulo `2`, since `(ZMod 2)ˣ` is trivial, so every
  character modulo `2` is the trivial one, of conductor `1`. Proved here, no input.
* `q = 6`: there is no primitive character modulo `6`, since every character modulo `6` factors
  through `ZMod 3`. This is a LEAF, a finite fact about `(ZMod 6)ˣ` and the conductor.
* `q = 3, 4, 5`: the window `(1, 2πe / q]` holds no strip zero at all. These are three LEAF
  zero free rectangles of one `L`-function each, at heights `2πe / 3 < 5.70`, `2πe / 4 < 4.28`, `2πe / 5 < 3.42`.
  Numerically, burst S97 with mpmath, the lowest positive zero ordinates of the primitive
  `L`-functions of these moduli lie above these heights: `8.04` for `q = 3`, `6.02` for
  `q = 4`, and for `q = 5` every zero found up to height `3.92` lies outside the window. An empty
  window is stronger than the parent conclusion, and it is what a zero verification such as
  the Turing method or the argument principle on the rectangle certifies.

The assembly is the case analysis on `q`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- No primitive character modulo `2`: `(ZMod 2)ˣ` is trivial, so the character is the trivial
one, of conductor `1 ≠ 2`. Proved, no input. -/
theorem card6_no_primitive_two (χ : DirichletCharacter ℂ q) (hq : q = 2) : ¬ χ.IsPrimitive := by
  subst hq
  intro hp
  have hu : ∀ a : (ZMod 2)ˣ, a = 1 := by decide
  have h1 : χ = 1 := by
    ext a
    rw [hu a]; simp
  have hc : χ.conductor = 1 := (DirichletCharacter.eq_one_iff_conductor_eq_one).mp h1
  rw [DirichletCharacter.isPrimitive_def, hc] at hp
  omega

/-- LEAF: modulus `6` case of the conductor block `2` to `6`, the fact that every Dirichlet
character modulo `6` factors through `ZMod 3`, since `(ZMod 6)ˣ → (ZMod 3)ˣ` is a bijection, so
its conductor divides `3` and no character modulo `6` is primitive. Class MEDIUM: finite
group facts about `(ZMod 6)ˣ` and `DirichletCharacter.FactorsThrough`. -/
theorem card6_no_primitive_six (χ : DirichletCharacter ℂ q) (hq : q = 6) : ¬ χ.IsPrimitive := by
  subst hq
  have h₃ : FactorsThrough χ 3 := by
    have hm : (3 : ℕ) ∣ 6 := by norm_num
    have h : (ZMod.unitsMap hm).ker ≤ χ.toUnitHom.ker := by
      intro x hx
      have h₁ : ((x.val : ZMod 6) : ZMod 3) = (1 : ZMod 3) := by
        have h₂ : ((unitsMap hm x : (ZMod 3)ˣ)) = (1 : (ZMod 3)ˣ) := MonoidHom.mem_ker hx
        have h₃ : ((unitsMap hm x) : ZMod 3) = (1 : ZMod 3) := by
          calc
            ((unitsMap hm x) : ZMod 3) = ((1 : (ZMod 3)ˣ) : ZMod 3) := by rw [h₂]
            _ = (1 : ZMod 3) := by simp [Units.val_one]
        have h₄ : ((unitsMap hm x) : ZMod 3) = ((x.val : ZMod 6) : ZMod 3) := by
          rw [unitsMap_val]
          <;> norm_cast
        linarith
      -- a unit modulo 6 is 1 or 5
      have h₂ : (x.val : ℕ) = 1 ∨ (x.val : ℕ) = 5 := by
        have h₂₁ : x.val < 6 := ZMod.natCast_self x.val
        have h₂₂ : (x.val : ℕ).Coprime 6 := by
          rw [ZMod.isUnit_iff_coprime] at x.isUnit
          exact x.isUnit
        have h₂₃ : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 5 :=
          by omega
        rcases h₂₃ with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
          (try { refine' Or.inl rfl }) <;>
          (try { refine' Or.inr rfl }) <;>
          (try {
            exfalso
            rw [ZMod.isUnit_iff_coprime] at x.isUnit
            norm_num [Nat.coprime] at x.isUnit ⊢ <;> contradiction
          })
      rcases h₂ with (rfl | rfl)
      · -- x.val = 1, so x = 1 and χ.toUnitHom x = 1
        have h₃ : x = 1 := by
          apply Units.ext_iff <;> norm_num [Units.val_one]
        rw [h₃]
        simp [MonoidHom.map_one]
      · -- x.val = 5 contradicts h₁
        exfalso
        have h₃ : ((x.val : ZMod 6) : ZMod 3) = (5 : ZMod 3) := by norm_num [ZMod.natCast_self]
        have h₄ : (5 : ZMod 3) ≠ (1 : ZMod 3) := by decide
        have h₅ : ((x.val : ZMod 6) : ZMod 3) = (1 : ZMod 3) := h₁
        have h₆ : (5 : ZMod 3) = (1 : ZMod 3) := by
          calc
            (5 : ZMod 3) = ((x.val : ZMod 6) : ZMod 3) := by rw [h₃]
            _ = (1 : ZMod 3) := h₅
        exact h₄ h₆
    exact (factorsThrough_iff_ker_unitsMap hm).mpr h
  have hc : χ.conductor ∣ 3 := by
    have h : (3 : ℕ) ∈ χ.conductorSet := by
      rw [mem_conductorSet_iff]
      exact h₃
    have h' : (3 : ℕ) ∣ 6 := by norm_num
    exact (mem_conductorSet_iff_conductor_dvd h').mp h
  intro h₆
  have h₇ : χ.conductor = 6 := by simpa [DirichletCharacter.isPrimitive_def] using h₆
  have h₈ : (6 : ℕ) ∣ 3 := by
    calc (6 : ℕ) = χ.conductor := by rw [h₇]
        _ ∣ 3 := hc
  norm_num at h₈

/-- LEAF: zero free rectangle for the primitive character modulo `3`, the window
`(1, 2πe / 3]` of the band at conductor `3` holds no strip zero of `L(·, χ)`. Numerically the
first zero of `L(s, χ₋₃)` is at height about `8.04`. Class HARD: a certified zero verification
of one `L`-function on a rectangle, argument principle or Turing method. -/
theorem card6_window_empty_three (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 3) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free rectangle for the primitive character modulo `4`, the window
`(1, 2πe / 4]` holds no strip zero of `L(·, χ)`. Numerically the first zero of `L(s, χ₋₄)` is at
height about `6.02`. Class HARD: a certified zero verification of one `L`-function. -/
theorem card6_window_empty_four (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 4) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free rectangle for the three primitive characters modulo `5`, the window
`(1, 2πe / 5]` holds no strip zero of `L(·, χ)`. Numerically no zero of these three
`L`-functions on the critical line has ordinate in that window. Class HARD: a certified zero
verification of three `L`-functions. -/
theorem card6_window_empty_five (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 5) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- Assembly of `book_count_band_above_one_mult_le_card_level_le_six` from the leaves: case analysis on `q` in `2` to `6`; the moduli `2`
and `6` carry no primitive character and the moduli `3`, `4`, `5` have an empty window. -/
theorem book_count_band_above_one_mult_le_card_level_le_six_of_leaves (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hq6 : q ≤ 6) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 := by omega
  rcases hcases with h | h | h | h | h
  · exact absurd hχ (card6_no_primitive_two χ h)
  · have h := card6_window_empty_three χ hχ h
    exact by rw [h]; simp
  · have h := card6_window_empty_four χ hχ h
    exact by rw [h]; simp
  · have h := card6_window_empty_five χ hχ h
    exact by rw [h]; simp
  · exact absurd hχ (card6_no_primitive_six χ h)

end LeanLab.HelfgottMajor.ZeroCount1623
