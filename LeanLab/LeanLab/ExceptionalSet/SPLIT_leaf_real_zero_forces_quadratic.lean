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
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 2, by linarith, ?_⟩
  intro P hP β hβ hβ1
  have hlogmono : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have hratio : Real.log 2 / 2 / Real.log P ≤ 1 / 2 := by
    rw [div_le_iff₀ hlog]
    linarith
  linarith

/-- A local nonvanishing statement for the Riemann zeta function at one, coming
from the simple pole: `(s - 1) * ζ s` tends to the nonzero residue `1`, so on a
small punctured ball around one `ζ` does not vanish. -/
private lemma exists_delta_riemannZeta_ne_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, s ≠ 1 → dist s 1 < δ → riemannZeta s ≠ 0 := by
  obtain ⟨δ, hδ, hδ'⟩ :=
    Metric.tendsto_nhdsWithin_nhds.1 riemannZeta_residue_one (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun s hs hdist hzero => ?_⟩
  have h := hδ' hs hdist
  rw [hzero, mul_zero] at h
  simp [Complex.dist_eq] at h
  norm_num at h

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
  obtain ⟨δ, hδ, hζ⟩ := exists_delta_riemannZeta_ne_zero
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min δ 1 * Real.log 2 / 2, by positivity, ?_⟩
  intro P hP q hq χ h1q hqP hprim hχ1 β hβ hβlow hβ1
  -- primitivity of the principal character forces level one
  have hq1 : q = 1 := by
    have h : χ.conductor = q := (DirichletCharacter.isPrimitive_def χ).1 hprim
    rw [hχ1, DirichletCharacter.conductor_one] at h
    exact h.symm
  subst hq1
  -- the character is now the one at level one, where `LFunction` is `riemannZeta`
  rw [DirichletCharacter.LFunction_modOne_eq]
  refine hζ (β : ℂ) ?_ ?_
  · intro h
    have hβeq : β = 1 := by exact_mod_cast h
    linarith
  · have hlogmono : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
    have hlog : 0 < Real.log P := Real.log_pos (by linarith)
    have hdist : dist (β : ℂ) 1 = 1 - β := by
      rw [Complex.dist_eq]
      have hsub : (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    have hratio : min δ 1 * Real.log 2 / 2 / Real.log P ≤ min δ 1 / 2 := by
      rw [div_le_iff₀ hlog]
      have hmul := mul_le_mul_of_nonneg_left hlogmono (le_of_lt (lt_min hδ one_pos))
      linarith
    have hminle : min δ 1 ≤ δ := min_le_left _ _
    have hone : min δ 1 ≤ 1 := min_le_right _ _
    rw [hdist]
    have hstep : 1 - β ≤ min δ 1 / 2 := by linarith
    linarith

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
  -- The imported file carries the Landau Page argument in full: its
  -- `leaf_real_zero_forces_quadratic` runs the lab zero free region
  -- `zero_free_region_real` at height zero and reads off `χ ^ 2 = 1` from the
  -- exceptional branch. The same width serves here.
  obtain ⟨a, ha, H⟩ := leaf_real_zero_forces_quadratic
  refine ⟨a, ha, ?_⟩
  intro P hP q hq χ h1q hqP hprim _ β _ hβ hβ1 hβ0
  exact (H P hP q hq χ h1q hqP hprim ⟨β, hβ, hβ1, hβ0⟩).1

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
