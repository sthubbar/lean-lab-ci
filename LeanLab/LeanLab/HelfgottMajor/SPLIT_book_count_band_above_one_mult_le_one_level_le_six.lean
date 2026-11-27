import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le
import LeanLab.HelfgottMajor.Feed1122BandZeroFree

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
  intro hprim
  -- Every character modulo 6 factors through modulo 3 because (ZMod 6)ˣ ≃ (ZMod 3)ˣ
  have h₁ : χ.FactorsThrough 3 := by
    -- The reduction map (ZMod 6)ˣ → (ZMod 3)ˣ is an isomorphism
    have h₂ : (3 : ℕ) ∣ 6 := by norm_num
    -- The kernel of (ZMod 6)ˣ → (ZMod 3)ˣ is trivial because both groups have order 2
    have h₃ : (ZMod.unitsMap h₂).ker = ⊥ := by
      apply Subgroup.eq_bot_iff.mpr
      intro x hx
      have h₄ : x = 1 := by
        -- The kernel consists of units in (ZMod 6)ˣ that map to 1 in (ZMod 3)ˣ
        -- The units of ZMod 6 are 1 and 5
        -- The units of ZMod 3 are 1 and 2
        -- 1 ↦ 1, 5 ↦ 2, so only 1 is in the kernel
        have h₅ : x.val = 1 ∨ x.val = 5 := by
          have : x.val = 1 ∨ x.val = 5 := by
            have h₆ : x.val = 1 ∨ x.val = 5 := by
              fin_cases x <;> norm_num at hx ⊢ <;> (try omega) <;> (try aesop)
            exact h₆
          exact this
        cases h₅ with
        | inl h₅ => simp_all [Units.ext_iff]
        | inr h₅ =>
          have h₆ := hx
          simp [ZMod.unitsMap_apply, ZMod.val_natCast, h₅] at h₆
          <;> norm_num at h₆ ⊢ <;> simp_all [Units.ext_iff]
      simp_all [Units.ext_iff]
    -- Since the kernel is trivial, the character factors through (ZMod 3)ˣ
    have h₄ : (ZMod.unitsMap h₂).ker ≤ χ.toUnitHom.ker := by
      rw [h₃]
      exact bot_le
    -- By the factorsThrough_iff_ker_unitsMap lemma, χ factors through 3
    have h₅ : χ.FactorsThrough 3 := by
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h₂]
      exact h₄
    exact h₅
  -- Since χ factors through 3, its conductor divides 3
  have h₂ : χ.conductor ∣ 3 := by
    have h₃ : χ.FactorsThrough 3 := h₁
    have h₄ : χ.conductor ∣ 3 := by
      -- The conductor is the minimal level through which χ factors
      have h₅ : χ.conductor ∣ 3 := by
        -- Use the fact that if χ factors through d, then conductor ∣ d
        have h₆ : χ.FactorsThrough 3 := h₁
        have h₇ : χ.conductor ∣ 3 := by
          -- The conductor divides any level through which χ factors
          have h₈ : χ.conductor ∣ 3 := by
            -- Use the property of conductor
            have h₉ : χ.conductor ∣ 3 := by
              apply Nat.dvd_trans (DirichletCharacter.factorsThrough_conductor χ).dvd
              exact h₆.dvd
            exact h₉
          exact h₈
        exact h₇
      exact h₅
    exact h₄
  -- Since the conductor divides 3, it cannot be 6
  have h₃ : χ.conductor ≠ 6 := by
    intro h
    have h₄ : χ.conductor ∣ 3 := h₂
    have h₅ : χ.conductor ≤ 3 := Nat.le_of_dvd (by norm_num) h₄
    omega
  -- A primitive character has conductor equal to its level (6)
  rw [DirichletCharacter.isPrimitive_def] at hprim
  apply h₃
  exact hprim

/-- LEAF: zero free rectangle for the primitive character modulo `3`, the window
`(1, 2πe / 3]` of the band at conductor `3` holds no strip zero of `L(·, χ)`. Numerically the
first zero of `L(s, χ₋₃)` is at height about `8.04`. Class HARD: a certified zero verification
of one `L`-function on a rectangle, argument principle or Turing method. -/
theorem one6_window_empty_three (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 3) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  have h₁ : ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (3 : ℝ)), ρ.im ≤ 1 := by
    -- This is the certified zero-free rectangle result for modulus 3.
    -- It requires a rigorous argument principle / Turing method verification
    -- that the primitive Dirichlet L-function modulo 3 has no zeros in the window.
    -- Currently available as a sorry in Feed1122BandZeroFree.band_window_zero_free_level_three.
    have h₂ := LeanLab.HelfgottMajor.Feed1122BandZeroFree.band_window_zero_free_level_three χ hχ (by norm_num [hq])
    simpa [hq] using h₂
  -- Convert the zero-free statement to the filtered finset being empty
  have h₂ : (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
    subst hq
    apply Finset.filter_eq_empty_iff.mpr
    intro ρ hρ
    have h₃ : ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (3 : ℝ))).toFinset := hρ.1
    have h₄ : 0 ≤ ρ.im ∧ 1 < ρ.im := hρ.2
    have h₅ : ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (3 : ℝ)) := (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (3 : ℝ))).mem_toFinset.mp h₃
    have h₆ : ρ.im ≤ 1 := h₁ ρ h₅
    linarith
  exact h₂

/-- LEAF: zero free rectangle for the primitive character modulo `4`, the window
`(1, 2πe / 4]` holds no strip zero of `L(·, χ)`. Numerically the first zero of `L(s, χ₋₄)` is at
height about `6.02`. Class HARD: a certified zero verification of one `L`-function. -/
theorem one6_window_empty_four (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 4) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  have h₁ : ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (4 : ℝ)), ρ.im ≤ 1 := by
    -- This is the certified zero-free rectangle result for modulus 4.
    -- It requires a rigorous argument principle / Turing method verification
    -- that the primitive Dirichlet L-function modulo 4 has no zeros in the window.
    -- Currently available as a sorry in Feed1122BandZeroFree.band_window_zero_free_level_four.
    have h₂ := LeanLab.HelfgottMajor.Feed1122BandZeroFree.band_window_zero_free_level_four χ hχ (by norm_num [hq])
    simpa [hq] using h₂
  -- Convert the zero-free statement to the filtered finset being empty
  have h₂ : (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
    subst hq
    apply Finset.filter_eq_empty_iff.mpr
    intro ρ hρ
    have h₃ : ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (4 : ℝ))).toFinset := hρ.1
    have h₄ : 0 ≤ ρ.im ∧ 1 < ρ.im := hρ.2
    have h₅ : ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (4 : ℝ)) := (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (4 : ℝ))).mem_toFinset.mp h₃
    have h₆ : ρ.im ≤ 1 := h₁ ρ h₅
    linarith
  exact h₂

/-- LEAF: zero free rectangle for the three primitive characters modulo `5`, the window
`(1, 2πe / 5]` holds no strip zero of `L(·, χ)`. Numerically no zero of these three
`L`-functions on the critical line has ordinate in that window. Class HARD: a certified zero
verification of three `L`-functions. -/
theorem one6_window_empty_five (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 5) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  have h₁ : ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (5 : ℝ)), ρ.im ≤ 1 := by
    -- This is the certified zero-free rectangle result for modulus 5.
    -- It requires a rigorous argument principle / Turing method verification
    -- that the three primitive Dirichlet L-functions modulo 5 have no zeros in the window.
    -- Currently available as a sorry in Feed1122BandZeroFree.band_window_zero_free_level_five.
    have h₂ := LeanLab.HelfgottMajor.Feed1122BandZeroFree.band_window_zero_free_level_five χ hχ (by norm_num [hq])
    simpa [hq] using h₂
  -- Convert the zero-free statement to the filtered finset being empty
  have h₂ : (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
    subst hq
    apply Finset.filter_eq_empty_iff.mpr
    intro ρ hρ
    have h₃ : ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (5 : ℝ))).toFinset := hρ.1
    have h₄ : 0 ≤ ρ.im ∧ 1 < ρ.im := hρ.2
    have h₅ : ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (5 : ℝ)) := (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (5 : ℝ))).mem_toFinset.mp h₃
    have h₆ : ρ.im ≤ 1 := h₁ ρ h₅
    linarith
  exact h₂

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
