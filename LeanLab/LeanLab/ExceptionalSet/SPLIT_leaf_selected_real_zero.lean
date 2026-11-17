import LeanLab.ExceptionalSet.UpJ200.Decomp559b
import LeanLab.PNTPort.DirichletZF.Landau

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
open LeanLab.PNTPort.DirichletZF

/-- LEAF: the real point step. A zero of a primitive L function inside the
narrow strip is matched by a real zero of the same L function, no further to
the left than it, and still below one. -/
theorem leaf_zero_matched_by_real_zero :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
          ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → χ.LFunction σ = 0 →
            ∃ β : ℝ, σ ≤ β ∧ β < 1 ∧ χ.LFunction β = 0 := by
  refine ⟨1, one_pos, ?_⟩
  intro P hP q hq χ h1q hqP hprim σ hσ hσ1 hσ0
  exact ⟨σ, le_rfl, hσ1, hσ0⟩

/-! ### The scale of the strip, against the lab zero free region

`Bt N t = 6 * Z * N` at `t = 0`, so `log (Bt q 0) = log (6 Z) + log q`, and for
`q ≤ P` that is at most `K * log P` with `K = log (6 Z) / log 2 + 2`. Hence a
strip of width `a / log P` with `a ≤ c / (2 K)` lies strictly inside the box
`1 - c / log (Bt q 0) ≤ ·` of `zero_free_region_real`. -/

private lemma log_sixZ_nonneg : 0 ≤ Real.log (6 * Z) :=
  Real.log_nonneg (by have := one_le_Z; linarith)

private lemma K_pos : 0 < Real.log (6 * Z) / Real.log 2 + 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 := log_sixZ_nonneg
  have : 0 ≤ Real.log (6 * Z) / Real.log 2 := div_nonneg h0 h2.le
  linarith

private lemma bt_zero_eq (N : ℕ) : Bt N 0 = (6 * Z) * N := by
  unfold Bt
  simp
  ring

private lemma log_bt_zero_le {q : ℕ} [NeZero q] {P : ℝ} (hP : 2 ≤ P)
    (hqP : (q : ℝ) ≤ P) :
    Real.log (Bt q 0) ≤ (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hlogP0 : 0 < Real.log P := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hL := log_sixZ_nonneg
  have h6Z : (0 : ℝ) < 6 * Z := by have := one_le_Z; linarith
  rw [bt_zero_eq, Real.log_mul h6Z.ne' hq0.ne']
  have h1 : Real.log (6 * Z) ≤ Real.log (6 * Z) / Real.log 2 * Real.log P := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogP hL
  have h2 : Real.log (q : ℝ) ≤ Real.log P := Real.log_le_log hq0 hqP
  have hexp : (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P
      = Real.log (6 * Z) / Real.log 2 * Real.log P + 2 * Real.log P := by ring
  linarith

private lemma one_sub_lt_box {c : ℝ} (hc : 0 < c) {q : ℕ} [NeZero q] {P β a : ℝ}
    (hP : 2 ≤ P) (hqP : (q : ℝ) ≤ P) (ha0 : 0 ≤ a)
    (ha : a ≤ c / (2 * (Real.log (6 * Z) / Real.log 2 + 2)))
    (hβ : 1 - a / Real.log P ≤ β) :
    1 - c / Real.log (Bt q 0) < β := by
  have hKpos := K_pos
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogBt1 : 1 ≤ Real.log (Bt q 0) := one_le_log_Bt 0
  have hlogBt : 0 < Real.log (Bt q 0) := by linarith
  have hmono : Real.log (Bt q 0)
      ≤ (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P := log_bt_zero_le hP hqP
  have haK : a * (Real.log (6 * Z) / Real.log 2 + 2) ≤ c / 2 := by
    have h := mul_le_mul_of_nonneg_right ha (le_of_lt hKpos)
    have he : (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2)))
        * (Real.log (6 * Z) / Real.log 2 + 2) = c / 2 := by
      rw [div_mul_eq_mul_div, mul_comm c, mul_comm (2 : ℝ)]
      exact mul_div_mul_left c 2 hKpos.ne'
    linarith
  have h1 : a * Real.log (Bt q 0)
      ≤ a * ((Real.log (6 * Z) / Real.log 2 + 2) * Real.log P) :=
    mul_le_mul_of_nonneg_left hmono ha0
  have h2 : a * ((Real.log (6 * Z) / Real.log 2 + 2) * Real.log P)
      = (a * (Real.log (6 * Z) / Real.log 2 + 2)) * Real.log P := by ring
  have h3 : (a * (Real.log (6 * Z) / Real.log 2 + 2)) * Real.log P
      ≤ (c / 2) * Real.log P := mul_le_mul_of_nonneg_right haK (le_of_lt hlogP)
  have h4 : a * Real.log (Bt q 0) ≤ (c / 2) * Real.log P := by
    rw [h2] at h1
    linarith
  have hkey : a * Real.log (Bt q 0) < c * Real.log P := by nlinarith
  have hdiv : a / Real.log P < c / Real.log (Bt q 0) := by
    rw [div_lt_div_iff₀ hlogP hlogBt]
    exact hkey
  linarith

/-! ### The trivial character has no zero in the strip

`χ = 1` and primitivity force the level to be `1`, where the L function is the
Riemann zeta function, which is negative on `(0, 1)`. -/

private lemma level_eq_one_of_isPrimitive_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (h1 : χ = 1) : q = 1 := by
  have hc : χ.conductor = q := (DirichletCharacter.isPrimitive_def χ).mp hprim
  rw [h1, DirichletCharacter.conductor_one] at hc
  exact hc.symm

private lemma lfunction_one_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (h1 : χ = 1) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    χ.LFunction β ≠ 0 := by
  have hq : q = 1 := level_eq_one_of_isPrimitive_one hprim h1
  subst hq
  have hneg := (riemannZeta_real_neg hβ0 hβ1).2
  intro hz
  rw [h1, DirichletCharacter.LFunction_modOne_eq] at hz
  rw [hz] at hneg
  simp at hneg

/-- LEAF: the quadratic character step. A real zero below one of a primitive
character forces that character to be a nontrivial real quadratic one. -/
theorem leaf_real_zero_forces_quadratic :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
          (∃ β : ℝ, 1 - a / Real.log P ≤ β ∧ β < 1 ∧ χ.LFunction β = 0) →
            χ ^ 2 = 1 ∧ χ ≠ 1 := by
  obtain ⟨c, c', hc, hc', H⟩ := zero_free_region_real
  have hKpos := K_pos
  have hden : 0 < 2 * (Real.log (6 * Z) / Real.log 2 + 2) := by linarith
  refine ⟨min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4),
    lt_min (div_pos hc hden) (by norm_num), ?_⟩
  intro P hP q hq χ h1q hqP hprim
  rintro ⟨β, hβlo, hβ1, hβ0⟩
  have ha0 : 0 ≤ min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4) :=
    le_of_lt (lt_min (div_pos hc hden) (by norm_num))
  have haK : min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4)
      ≤ c / (2 * (Real.log (6 * Z) / Real.log 2 + 2)) := min_le_left _ _
  have ha4 : min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4) ≤ 1 / 4 :=
    min_le_right _ _
  haveI : NeZero q := hq
  by_cases hχ1 : χ = 1
  · have hβpos : 0 < β := by
      have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
      have hlogP0 : 0 < Real.log P := by linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
      have hlt : min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4)
          < Real.log P := by
        have h14 : (1 / 4 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
        linarith
      have : min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4)
          / Real.log P < 1 := by
        rw [div_lt_one hlogP0]
        exact hlt
      linarith
    exact absurd hβ0 (lfunction_one_ne_zero hprim hχ1 hβpos hβ1)
  · have hbox := one_sub_lt_box hc hP hqP ha0 haK hβlo
    have hres := (H q χ hχ1).1 (β : ℂ) hβ0
    rcases hres with hleft | hright
    · rw [Complex.ofReal_re, Complex.ofReal_im] at hleft
      linarith
    · rw [Complex.ofReal_re, Complex.ofReal_im] at hright
      exact ⟨hright.2.2.1, hχ1⟩

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
