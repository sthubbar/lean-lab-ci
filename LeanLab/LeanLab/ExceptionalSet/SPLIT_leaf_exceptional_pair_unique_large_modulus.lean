import LeanLab.ExceptionalSet.SPLIT_leaf_exceptional_pair_unique

/-!
Split of `leaf_exceptional_pair_unique_large_modulus` of
`LeanLab.ExceptionalSet.SPLIT_leaf_exceptional_pair_unique`.

Paper: Brüdern and Perelli 1998, P0082 page 358 display 9, citing Davenport chapter 14.

The leaf asks that a real primitive character of modulus `r > P` with a zero in the strip
`[1 - a / log P, 1)` leaves no zero in that strip for a primitive character of modulus at most
`P`.  For moduli `P < r ≤ P ^ 2` this is proved here as `exceptional_pair_unique_mid_modulus`:
then `log r ≤ 2 log P`, so a strip of width `a / log P` with `a ≤ c / 2` sits inside Landau's
strip of width `c / log r`, Landau's theorem `landau` at `Q = r` identifies the two characters
after lifting, and primitivity forces equal moduli, impossible as `q ≤ P < r`.  The residual
range `r > P ^ 2` is the single LEAF `leaf_exceptional_pair_unique_huge_modulus`; there the
strip of the leaf is wider than Landau's, and the same QUESTION as for the parent applies.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b
open Real Finset Filter
open LeanLab.PNTPort.DirichletZF

private lemma mm_level_eq_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (h1 : χ = 1) : q = 1 := by
  have hc : χ.conductor = q := (DirichletCharacter.isPrimitive_def χ).mp hprim
  rw [h1, DirichletCharacter.conductor_one] at hc
  exact hc.symm

private lemma mm_one_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (h1 : χ = 1) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    χ.LFunction β ≠ 0 := by
  have hq : q = 1 := mm_level_eq_one hprim h1
  subst hq
  have hneg := (riemannZeta_real_neg hβ0 hβ1).2
  intro hz
  rw [h1, DirichletCharacter.LFunction_modOne_eq] at hz
  rw [hz] at hneg
  simp at hneg

private lemma mm_level_eq_of_lift_eq (q r M : ℕ) [NeZero M]
    (ψ : DirichletCharacter ℂ q) (χ : DirichletCharacter ℂ r)
    (hψ : ψ.IsPrimitive) (hχ : χ.IsPrimitive) (hq : q ∣ M) (hr : r ∣ M)
    (heq : DirichletCharacter.changeLevel hq ψ = DirichletCharacter.changeLevel hr χ) :
    q = r :=
  calc
    q = ψ.conductor := hψ.symm
    _ = (DirichletCharacter.changeLevel hq ψ).conductor :=
      (DirichletCharacter.conductor_changeLevel ψ hq).symm
    _ = (DirichletCharacter.changeLevel hr χ).conductor := congrArg _ heq
    _ = χ.conductor := DirichletCharacter.conductor_changeLevel χ hr
    _ = r := hχ

/-- Proved: the large modulus leaf in the range `P < r ≤ P ^ 2`, from Landau's theorem at
`Q = r`. -/
theorem exceptional_pair_unique_mid_modulus :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ), P < (r : ℝ) →
        (r : ℝ) ≤ P ^ 2 →
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
          1 - a / Real.log P ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
              1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
                ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → ψ.LFunction σ = 0 → False := by
  obtain ⟨cL, hcL, hL⟩ := landau
  refine ⟨min (cL / 2) (1 / 2), lt_min (by positivity) (by norm_num), ?_⟩
  intro P hP r hr χ β hPr hrP2 hχp _ hχ1 _ hβa hβ1 hβz q hq ψ _ hqP hψp σ hσa hσ1 hσz
  set a : ℝ := min (cL / 2) (1 / 2) with ha_def
  have haL : a ≤ cL / 2 := min_le_left _ _
  have ha2 : a ≤ 1 / 2 := min_le_right _ _
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogP2 : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hσ0 : 0 < σ := by
    have : a / Real.log P < 1 := by
      rw [div_lt_one hlogP]; linarith
    linarith
  have hψ1 : ψ ≠ 1 := fun h => mm_one_ne_zero hψp h hσ0 hσ1 hσz
  have hr2 : 2 ≤ r := by
    have : (2 : ℝ) < r := lt_of_le_of_lt hP hPr
    exact_mod_cast this.le
  have hqr : q ≤ r := by
    have : (q : ℝ) ≤ r := le_trans hqP hPr.le
    exact_mod_cast this
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos (by linarith)
  have hlogr2 : Real.log (r : ℝ) ≤ 2 * Real.log P := by
    have h := Real.log_le_log hr0 hrP2
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hstrip : ∀ x : ℝ, 1 - a / Real.log P ≤ x → 1 - cL / Real.log (r : ℝ) ≤ x := by
    intro x hx
    have h1 : a / Real.log P ≤ (cL / 2) / Real.log P :=
      div_le_div_of_nonneg_right haL hlogP.le
    have h2 : (cL / 2) / Real.log P ≤ cL / Real.log (r : ℝ) := by
      rw [div_le_div_iff₀ hlogP hlogr]
      nlinarith
    linarith
  have hlift := hL r hr2 q r hqr le_rfl ψ χ hψ1 hχ1 σ β hσ1.le hβ1.le hσz hβz
    (hstrip σ hσa) (hstrip β hβa)
  have : NeZero (q * r) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  have hqr' := mm_level_eq_of_lift_eq q r (q * r) ψ χ hψp hχp _ _ hlift
  have : (r : ℝ) ≤ P := by rw [← hqr']; exact hqP
  linarith

/-- LEAF: P0082 page 358 display 9, uniqueness of the exceptional pair, residual range of the
large modulus case where the given exceptional modulus `r` exceeds `P ^ 2`. HARD. Not used by
the paper, whose exceptional modulus is at most `P`; see the QUESTION in the notes. -/
theorem leaf_exceptional_pair_unique_huge_modulus :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ), P ^ 2 < (r : ℝ) →
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
          1 - a / Real.log P ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
              1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
                ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → ψ.LFunction σ = 0 → False := by
  sorry

/-- Assembly of `leaf_exceptional_pair_unique_large_modulus` from the proved middle range and
the residual leaf, with the smaller of the two widths. -/
theorem leaf_exceptional_pair_unique_large_modulus_split :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ), P < (r : ℝ) →
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
          1 - a / Real.log P ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
              1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
                ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → ψ.LFunction σ = 0 → False := by
  obtain ⟨a₁, ha₁, H₁⟩ := exceptional_pair_unique_mid_modulus
  obtain ⟨a₂, ha₂, H₂⟩ := leaf_exceptional_pair_unique_huge_modulus
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, ?_⟩
  intro P hP r hr χ β hPr hχp hχ2 hχ1 hβ0 hβa hβ1 hβz q hq ψ h1q hqP hψp σ hσa hσ1 hσz
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hw : ∀ b : ℝ, min a₁ a₂ ≤ b → ∀ x : ℝ, 1 - min a₁ a₂ / Real.log P ≤ x →
      1 - b / Real.log P ≤ x := by
    intro b hb x hx
    have := div_le_div_of_nonneg_right hb hlogP.le
    linarith
  by_cases hr2 : (r : ℝ) ≤ P ^ 2
  · exact H₁ P hP r hr χ β hPr hr2 hχp hχ2 hχ1 hβ0 (hw a₁ (min_le_left _ _) β hβa) hβ1 hβz
      q hq ψ h1q hqP hψp σ (hw a₁ (min_le_left _ _) σ hσa) hσ1 hσz
  · exact H₂ P hP r hr χ β (not_le.mp hr2) hχp hχ2 hχ1 hβ0
      (hw a₂ (min_le_right _ _) β hβa) hβ1 hβz
      q hq ψ h1q hqP hψp σ (hw a₂ (min_le_right _ _) σ hσa) hσ1 hσz

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
