import LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-!
Splitting the selection of one exceptional real zero in `Decomp559b`.

The imported statement fixes one positive width and then, for every range,
either a strip free of primitive zeros or one real quadratic character whose
zero is the only one in that strip. The three leaves below are the separate
steps that build it: a primitive zero inside the narrow strip is matched by a
real zero of the same function no further to the left, a real zero inside the
strip forces a nontrivial real quadratic character, and for a small enough
width the exceptional pair inside the strip is unique.

No new definition is introduced here, and the assembly closes the imported
statement from the three leaves.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b
open Real Finset Filter
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- LEAF: the real point step. A zero of a primitive L function inside the
narrow strip is matched by a real zero of the same L function, no further to
the left than it, and still below one. -/
theorem leaf_zero_matched_by_real_zero :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
          ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → χ.LFunction σ = 0 →
            ∃ β : ℝ, σ ≤ β ∧ β < 1 ∧ χ.LFunction β = 0 := by
  sorry

/-- LEAF: the quadratic character step. A real zero below one of a primitive
character forces that character to be a nontrivial real quadratic one. -/
theorem leaf_real_zero_forces_quadratic :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
          (∃ β : ℝ, 1 - a / Real.log P ≤ β ∧ β < 1 ∧ χ.LFunction β = 0) →
            χ ^ 2 = 1 ∧ χ ≠ 1 := by
  sorry

/-- LEAF: the uniqueness step. For a small enough width the exceptional pair in
the strip is unique: no second primitive character of modulus at most P has a
zero in that strip. -/
theorem leaf_exceptional_pair_unique :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
          1 - a / Real.log P ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
              1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
                ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → ψ.LFunction σ = 0 →
                  q = r ∧ HEq ψ χ ∧ σ = β := by
  sorry

/-- The selection statement of the imported file, closed from the three leaves
above: one positive width, and for every range either no primitive zero in the
strip or one real quadratic character carrying the only zero there. -/
theorem leaf_selected_real_zero_split :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ P ∧ SelectedRealZero a P r := by
  obtain ⟨a₁, ha₁, hreal⟩ := leaf_zero_matched_by_real_zero
  obtain ⟨a₂, ha₂, hquad⟩ := leaf_real_zero_forces_quadratic
  obtain ⟨a₃, ha₃, huniq⟩ := leaf_exceptional_pair_unique
  set a : ℝ := min a₁ (min a₂ (min a₃ (1 / 2))) with haeq
  have ha : 0 < a := lt_min ha₁ (lt_min ha₂ (lt_min ha₃ (by norm_num)))
  have h₁ : a ≤ a₁ := min_le_left _ _
  have h₂ : a ≤ a₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h₃ : a ≤ a₃ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh : a ≤ 1 / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a, ha, ?_⟩
  intro P hP
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlogmono : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hshallow : a / Real.log P < 1 := by
    rw [div_lt_one hlog]
    exact lt_of_le_of_lt hh (lt_of_lt_of_le hlogtwo hlogmono)
  by_cases hfree : ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
        ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → χ.LFunction σ ≠ 0
  · have hone : ((1 : ℕ) : ℝ) ≤ P := by push_cast; linarith
    exact ⟨1, le_rfl, hone, Or.inl ⟨rfl, hfree⟩⟩
  · push Not at hfree
    obtain ⟨q, hq, χ, h1q, hqP, hprim, σ, hσ, hσ1, hσ0⟩ := hfree
    have hσa : 1 - a₁ / Real.log P ≤ σ := by
      have h := div_le_div_of_nonneg_right h₁ hlog.le
      linarith
    obtain ⟨β, hσβ, hβ1, hβ0⟩ := hreal P hP q hq χ h1q hqP hprim σ hσa hσ1 hσ0
    have hβpos : 0 < β := by
      have hgt : 0 < 1 - a / Real.log P := by linarith
      linarith
    have hβa : 1 - a / Real.log P ≤ β := by linarith
    have hβa₂ : 1 - a₂ / Real.log P ≤ β := by
      have h := div_le_div_of_nonneg_right h₂ hlog.le
      linarith
    obtain ⟨hχ2, hχ1⟩ := hquad P hP q hq χ h1q hqP hprim ⟨β, hβa₂, hβ1, hβ0⟩
    have hβa₃ : 1 - a₃ / Real.log P ≤ β := by
      have h := div_le_div_of_nonneg_right h₃ hlog.le
      linarith
    refine ⟨q, h1q, hqP, Or.inr ⟨hq, χ, β, hprim, hχ2, hχ1, hβpos, hβa, hβ1, hβ0, ?_⟩⟩
    intro q' hq' ψ h1q' hq'P hψprim τ hτ hτ1 hτ0
    have hτa₃ : 1 - a₃ / Real.log P ≤ τ := by
      have h := div_le_div_of_nonneg_right h₃ hlog.le
      linarith
    exact huniq P hP q hq χ β hprim hχ2 hχ1 hβpos hβa₃ hβ1 hβ0
      q' hq' ψ h1q' hq'P hψprim τ hτa₃ hτ1 hτ0
