import LeanLab.ExceptionalSet.SPLIT_leaf_selected_real_zero

/-!
Splitting the quadratic character step of `SPLIT_leaf_selected_real_zero`.

The imported statement fixes one positive width and then, for every range,
either a strip free of primitive zeros or one real quadratic character whose
zero is the only one in that strip. The step cut here is its middle leaf: a real
zero of a primitive `L` function just below one forces the character to be a
nontrivial real quadratic one.

Three smaller steps build it. The strip of the stated width lies inside `(0, 1)`,
so a zero in it is a positive real number below one. At such a point the
principal character has no zero, because a primitive principal character has
level one and the `L` function there is the Riemann zeta function, which is
negative on `(0, 1)`. Away from the principal character a real zero below one is
the exceptional zero of the lab zero free region: either it sits at distance at
least a fixed multiple of `1 / log` of the level from one, which the strip
forbids for a small enough width, or its character is real.

No new definition is introduced here, and the assembly closes the cut statement
from the three steps.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b
open Real Finset Filter
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- LEAF: the strip lies inside `(0, 1)`. For a width at most `1 / 4` the lower
edge `1 - a / Real.log P` of the strip is positive, because `1 / 4 < log 2` and
`log 2 ≤ log P`, so every point of the strip is a positive real number. -/
theorem leaf_strip_lower_edge_pos :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ β : ℝ, 1 - a / Real.log P ≤ β → β < 1 → 0 < β := by
  sorry

/-- LEAF: the principal character has no zero in the strip. A primitive
principal character of level `q` has `q = 1`, and there the `L` function is the
Riemann zeta function, which does not vanish at a positive real point below
one. -/
theorem leaf_principal_no_strip_zero :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive → χ = 1 →
          ∀ β : ℝ, 0 < β → 1 - a / Real.log P ≤ β → β < 1 →
            χ.LFunction β ≠ 0 := by
  sorry

/-- LEAF: a non-principal character with a real zero in the strip is real
quadratic. The lab zero free region puts such a zero either at distance at least
a fixed multiple of `1 / log` of the level from one, which a small enough width
forbids, or else at the single exceptional zero, whose character is real. -/
theorem leaf_nonprincipal_strip_forces_quadratic :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive → χ ≠ 1 →
          ∀ β : ℝ, 0 < β → 1 - a / Real.log P ≤ β → β < 1 →
            χ.LFunction β = 0 → χ ^ 2 = 1 := by
  sorry

/-- The quadratic character step of the imported file, closed from the three
leaves above: one positive width, and every primitive character with a real zero
that close to one is a nontrivial real quadratic character. -/
theorem leaf_real_zero_forces_quadratic_split :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
          (∃ β : ℝ, 1 - a / Real.log P ≤ β ∧ β < 1 ∧ χ.LFunction β = 0) →
            χ ^ 2 = 1 ∧ χ ≠ 1 := by
  obtain ⟨a₁, ha₁, hpos⟩ := leaf_strip_lower_edge_pos
  obtain ⟨a₂, ha₂, hprin⟩ := leaf_principal_no_strip_zero
  obtain ⟨a₃, ha₃, hquad⟩ := leaf_nonprincipal_strip_forces_quadratic
  refine ⟨min a₁ (min a₂ a₃), lt_min ha₁ (lt_min ha₂ ha₃), ?_⟩
  intro P hP q hq χ h1q hqP hprim
  rintro ⟨β, hβ, hβ1, hβ0⟩
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have hle₁ : min a₁ (min a₂ a₃) ≤ a₁ := min_le_left _ _
  have hle₂ : min a₁ (min a₂ a₃) ≤ a₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₃ : min a₁ (min a₂ a₃) ≤ a₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hmono : ∀ a' : ℝ, min a₁ (min a₂ a₃) ≤ a' → 1 - a' / Real.log P ≤ β := by
    intro a' ha'
    have h := div_le_div_of_nonneg_right ha' hlog.le
    linarith
  have hβpos : 0 < β := hpos P hP β (hmono a₁ hle₁) hβ1
  by_cases h1 : χ = 1
  · exact absurd hβ0
      (hprin P hP q hq χ h1q hqP hprim h1 β hβpos (hmono a₂ hle₂) hβ1)
  · refine ⟨?_, h1⟩
    by_contra h2
    exact h2 (hquad P hP q hq χ h1q hqP hprim h1 β hβpos (hmono a₃ hle₃) hβ1 hβ0)
