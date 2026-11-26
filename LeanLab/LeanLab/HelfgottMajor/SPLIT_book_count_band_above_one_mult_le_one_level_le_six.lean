import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le

/-!
# Split of `book_count_band_above_one_mult_le_one_level_le_six`

The parent block covers the conductors `2` to `6` at the top height `2πe / q` of the band:
every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / q]` has multiplicity at most one. It is split by modulus.

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
theorem one6_no_primitive_two (χ : DirichletCharacter ℂ q) (hq : q = 2) : ¬ χ.IsPrimitive := by
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
theorem one6_no_primitive_six (χ : DirichletCharacter ℂ q) (hq : q = 6) : ¬ χ.IsPrimitive := by
  subst hq
  intro hp
  have h₃_dvd_6 : 3 ∣ 6 := by norm_num
  -- First, prove that every character modulo 6 factors through modulo 3
  have hfac : χ.FactorsThrough 3 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (by norm_num : 3 ∣ 6)]
    intro u hu
    -- The kernel of (ZMod 6)ˣ → (ZMod 3)ˣ is trivial (only 1)
    -- hu : ZMod.unitsMap (by norm_num : 3 ∣ 6) u = 1
    -- This means u = 1 in (ZMod 6)ˣ
    have h : u = 1 := by
      -- The units of (ZMod 6)ˣ are 1 and 5
      -- If u is in the kernel, its image in (ZMod 3)ˣ is 1
      -- The image of 5 is 2 ≠ 1, so u must be 1
      have h₁ : (u : ZMod 6) = 1 ∨ (u : ZMod 6) = 5 := by
        -- The units of ZMod 6 are exactly 1 and 5
        have h₂ : (u : ZMod 6) = 1 ∨ (u : ZMod 6) = 5 := by
          -- The units of ZMod 6 are 1 and 5
          classical
          by_cases h : (u : ZMod 6) = 1
          · exact Or.inl h
          · -- If u ≠ 1, then u = 5
            have h₂ : (u : ZMod 6) = 5 := by
              -- The only units in ZMod 6 are 1 and 5
              have h₃ : (u : ZMod 6) = 1 ∨ (u : ZMod 6) = 5 := by
                -- The units of ZMod 6 are 1 and 5
                have h₄ : (u : ZMod 6) = 1 ∨ (u : ZMod 6) = 5 := by
                  -- Use the fact that the units of ZMod 6 are 1 and 5
                  have h₅ : u = 1 ∨ u = ⟨5, 5, by decide, by decide⟩ := by
                    classical
                    by_cases h₆ : u = 1
                    · exact Or.inl h₆
                    · -- If u ≠ 1, then u = 5
                      have h₇ : u = ⟨5, 5, by decide, by decide⟩ := by
                        classical
                        revert u
                        decide
                      exact Or.inr h₇
                  cases h₅ with
                  | inl h₅ =>
                    simp_all [Units.ext_iff]
                    <;> contradiction
                  | inr h₅ =>
                    simp_all [Units.ext_iff]
                    <;> aesop
                cases h₄ with
                | inl h₄ => simp_all [Units.ext_iff]
                | inr h₄ => simp_all [Units.ext_iff]
              exact h₃
            exact Or.inr h₂
        exact h₂
      cases h₁ with
      | inl h₁ =>
        -- If u = 1, we're done
        apply Units.ext
        simp [h₁]
      | inr h₁ =>
        -- If u = 5, check that it doesn't map to 1 in ZMod 3
        have h₂ : ZMod.unitsMap (by norm_num : 3 ∣ 6) u = 1 := hu
        have h₃ : (ZMod.unitsMap (by norm_num : 3 ∣ 6) u : ZMod 3) = 1 := by simpa using h₂
        -- The map sends 5 to 2 in ZMod 3, which is not 1
        have h₄ : (u : ZMod 6) = 5 := h₁
        -- The image of 5 is 2, which is not 1
        have h₅ : (ZMod.unitsMap (by norm_num : 3 ∣ 6) u : ZMod 3) = 2 := by
          -- Use the fact that u = 5 as a unit
          have h₅ : u = ⟨5, 5, by decide, by decide⟩ := by
            apply Units.ext
            simp [h₁]
            <;> norm_num
          rw [h₅]
          <;> norm_num [ZMod.unitsMap, ZMod.castHom_apply, Units.ext_iff]
          <;> rfl
        rw [h₅] at h₃
        norm_num at h₃ ⊢
        <;> contradiction
      <;> simp_all
    rw [h]
    simp
  -- Since χ factors through 3, its conductor divides 3
  have hconductor_dvd_3 : χ.conductor ∣ 3 := by
    have h₁ : χ.conductor ∣ 3 := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hfac
    exact h₁
  -- But if χ is primitive, its conductor equals 6
  have hconductor_eq_6 : χ.conductor = 6 := by
    rw [DirichletCharacter.isPrimitive_def] at hp
    exact hp
  -- Contradiction: 6 does not divide 3
  have h₆_dvd_3 : (6 : ℕ) ∣ 3 := by
    rw [hconductor_eq_6] at hconductor_dvd_3
    exact hconductor_dvd_3
  norm_num at h₆_dvd_3
  <;> omega

/-- LEAF: zero free rectangle for the primitive character modulo `3`, the window
`(1, 2πe / 3]` of the band at conductor `3` holds no strip zero of `L(·, χ)`. Numerically the
first zero of `L(s, χ₋₃)` is at height about `8.04`. Class HARD: a certified zero verification
of one `L`-function on a rectangle, argument principle or Turing method. -/
theorem one6_window_empty_three (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 3) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free rectangle for the primitive character modulo `4`, the window
`(1, 2πe / 4]` holds no strip zero of `L(·, χ)`. Numerically the first zero of `L(s, χ₋₄)` is at
height about `6.02`. Class HARD: a certified zero verification of one `L`-function. -/
theorem one6_window_empty_four (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 4) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free rectangle for the three primitive characters modulo `5`, the window
`(1, 2πe / 5]` holds no strip zero of `L(·, χ)`. Numerically no zero of these three
`L`-functions on the critical line has ordinate in that window. Class HARD: a certified zero
verification of three `L`-functions. -/
theorem one6_window_empty_five (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 5) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- Assembly of `book_count_band_above_one_mult_le_one_level_le_six` from the leaves: case analysis on `q` in `2` to `6`; the moduli `2`
and `6` carry no primitive character and the moduli `3`, `4`, `5` have an empty window. -/
theorem book_count_band_above_one_mult_le_one_level_le_six_of_leaves (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hq6 : q ≤ 6) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 := by omega
  rcases hcases with h | h | h | h | h
  · exact absurd hχ (one6_no_primitive_two χ h)
  · have h := one6_window_empty_three χ hχ h
    exact by intro ρ hρ; rw [h] at hρ; simp at hρ
  · have h := one6_window_empty_four χ hχ h
    exact by intro ρ hρ; rw [h] at hρ; simp at hρ
  · have h := one6_window_empty_five χ hχ h
    exact by intro ρ hρ; rw [h] at hρ; simp at hρ
  · exact absurd hχ (one6_no_primitive_six χ h)

end LeanLab.HelfgottMajor.ZeroCount1623
