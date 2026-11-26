import LeanLab.ExceptionalSet.SPLIT_leaf_selected_real_zero
import LeanLab.PNTPort.DirichletZF.Page

/-!
Split of `leaf_exceptional_pair_unique` of `LeanLab.ExceptionalSet.SPLIT_leaf_selected_real_zero`.

Paper: Brüdern and Perelli 1998, P0082 page 358 display 9 and the paragraph before display
10, which cite Davenport chapter 14 for the uniqueness of the exceptional character among the
primitive characters of modulus at most `P`, and for the uniqueness of its zero.

The statement being split does not bound the modulus `r` of the given exceptional character
by `P`.  The paper only uses the case `r ≤ P`, where the exceptional character is one of the
characters of modulus at most `P`.  That case is proved here in full as
`exceptional_pair_unique_bounded`: Landau's theorem `landau` of the lab, proved in
`LeanLab.PNTPort.DirichletZF.Landau`, identifies the two characters after lifting to the
product modulus, primitivity then identifies the moduli and the characters, and Page's
theorem `page_two_zeros` of `LeanLab.PNTPort.DirichletZF.Page` identifies the two zeros.  The
principal character is excluded since the Riemann zeta function is negative on `(0, 1)`.

The remaining case `P < r` is the single LEAF `leaf_exceptional_pair_unique_large_modulus`.
There the conclusion `q = r` is impossible because `q ≤ P`, so the leaf asserts that no
primitive character of modulus at most `P` has a zero in the strip while a real character of a
larger modulus does.  This case is not in the paper and is not covered by Landau's theorem,
whose strip shrinks with `log r`; see the QUESTION in the notes.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b
open Real Finset Filter
open LeanLab.PNTPort.DirichletZF

private lemma pu_log_sixZ_nonneg : 0 ≤ Real.log (6 * Z) :=
  Real.log_nonneg (by have := one_le_Z; linarith)

private lemma pu_K_pos : 0 < Real.log (6 * Z) / Real.log 2 + 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 := pu_log_sixZ_nonneg
  have : 0 ≤ Real.log (6 * Z) / Real.log 2 := div_nonneg h0 h2.le
  linarith

private lemma pu_bt_zero_eq (N : ℕ) : Bt N 0 = (6 * Z) * N := by
  unfold Bt
  simp
  ring

private lemma pu_log_bt_zero_le {q : ℕ} [NeZero q] {P : ℝ} (hP : 2 ≤ P)
    (hqP : (q : ℝ) ≤ P) :
    Real.log (Bt q 0) ≤ (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hL := pu_log_sixZ_nonneg
  have h6Z : (0 : ℝ) < 6 * Z := by have := one_le_Z; linarith
  rw [pu_bt_zero_eq, Real.log_mul h6Z.ne' hq0.ne']
  have h1 : Real.log (6 * Z) ≤ Real.log (6 * Z) / Real.log 2 * Real.log P := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogP hL
  have h2 : Real.log (q : ℝ) ≤ Real.log P := Real.log_le_log hq0 hqP
  have hexp : (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P
      = Real.log (6 * Z) / Real.log 2 * Real.log P + 2 * Real.log P := by ring
  linarith

/-- A strip of width `a / log P` with `a ≤ c / K` sits inside Page's box at modulus `q ≤ P`. -/
private lemma pu_box {c : ℝ} (_hc : 0 < c) {q : ℕ} [NeZero q] {P β a : ℝ}
    (hP : 2 ≤ P) (hqP : (q : ℝ) ≤ P) (ha0 : 0 ≤ a)
    (ha : a ≤ c / (Real.log (6 * Z) / Real.log 2 + 2))
    (hβ : 1 - a / Real.log P ≤ β) :
    1 - c / Real.log (Bt q 0) ≤ β := by
  have hK := pu_K_pos
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogBt : 0 < Real.log (Bt q 0) := by linarith [one_le_log_Bt (N := q) 0]
  have hmono := pu_log_bt_zero_le hP hqP
  have haK : a * (Real.log (6 * Z) / Real.log 2 + 2) ≤ c := by
    rwa [le_div_iff₀ hK] at ha
  have h1 : a * Real.log (Bt q 0) ≤ c * Real.log P := by
    calc a * Real.log (Bt q 0)
        ≤ a * ((Real.log (6 * Z) / Real.log 2 + 2) * Real.log P) :=
          mul_le_mul_of_nonneg_left hmono ha0
      _ = (a * (Real.log (6 * Z) / Real.log 2 + 2)) * Real.log P := by ring
      _ ≤ c * Real.log P := mul_le_mul_of_nonneg_right haK hlogP.le
  have hdiv : a / Real.log P ≤ c / Real.log (Bt q 0) := by
    rw [div_le_div_iff₀ hlogP hlogBt]
    exact h1
  linarith

private lemma pu_level_eq_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (h1 : χ = 1) : q = 1 := by
  have hc : χ.conductor = q := (DirichletCharacter.isPrimitive_def χ).mp hprim
  rw [h1, DirichletCharacter.conductor_one] at hc
  exact hc.symm

private lemma pu_one_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (h1 : χ = 1) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    χ.LFunction β ≠ 0 := by
  have hq : q = 1 := pu_level_eq_one hprim h1
  subst hq
  have hneg := (riemannZeta_real_neg hβ0 hβ1).2
  intro hz
  rw [h1, DirichletCharacter.LFunction_modOne_eq] at hz
  rw [hz] at hneg
  simp at hneg

private lemma pu_primitive_eq_of_lift_eq (q r M : ℕ) [NeZero M]
    (ψ : DirichletCharacter ℂ q) (χ : DirichletCharacter ℂ r)
    (hψ : ψ.IsPrimitive) (hχ : χ.IsPrimitive) (hq : q ∣ M) (hr : r ∣ M)
    (heq : DirichletCharacter.changeLevel hq ψ = DirichletCharacter.changeLevel hr χ) :
    q = r ∧ HEq ψ χ := by
  have hlevel : q = r := by
    calc
      q = ψ.conductor := hψ.symm
      _ = (DirichletCharacter.changeLevel hq ψ).conductor :=
        (DirichletCharacter.conductor_changeLevel ψ hq).symm
      _ = (DirichletCharacter.changeLevel hr χ).conductor := congrArg _ heq
      _ = χ.conductor := DirichletCharacter.conductor_changeLevel χ hr
      _ = r := hχ
  subst hlevel
  exact ⟨rfl, heq_of_eq (DirichletCharacter.changeLevel_injective hq heq)⟩

/-- Proved: the uniqueness step of P0082 page 358 display 9 in the case the paper uses, where
the exceptional modulus `r` is itself at most `P`.  Landau's theorem identifies the
characters, Page's theorem identifies the zeros. -/
theorem exceptional_pair_unique_bounded :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ), (r : ℝ) ≤ P →
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
          1 - a / Real.log P ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
              1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
                ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → ψ.LFunction σ = 0 →
                  q = r ∧ HEq ψ χ ∧ σ = β := by
  obtain ⟨cL, hcL, hL⟩ := landau
  obtain ⟨cP, hcP, hPg⟩ := page_two_zeros
  have hK := pu_K_pos
  set a : ℝ := min cL (min (cP / (Real.log (6 * Z) / Real.log 2 + 2)) (1 / 2)) with ha_def
  have ha : 0 < a := lt_min hcL (lt_min (div_pos hcP hK) (by norm_num))
  have haL : a ≤ cL := min_le_left _ _
  have haP : a ≤ cP / (Real.log (6 * Z) / Real.log 2 + 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have ha2 : a ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨a, ha, ?_⟩
  intro P hP r hr χ β hrP hχp hχ2 hχ1 hβ0 hβa hβ1 hβz q hq ψ h1q hqP hψp σ hσa hσ1 hσz
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogP2 : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hσ0 : 0 < σ := by
    have : a / Real.log P < 1 := by
      rw [div_lt_one hlogP]; linarith
    linarith
  -- the second character is not principal
  have hψ1 : ψ ≠ 1 := fun h => pu_one_ne_zero hψp h hσ0 hσ1 hσz
  -- Landau at `Q = ⌊P⌋₊`
  set Q : ℕ := ⌊P⌋₊ with hQ
  have hQ2 : 2 ≤ Q := Nat.le_floor (by exact_mod_cast hP)
  have hqQ : q ≤ Q := Nat.le_floor hqP
  have hrQ : r ≤ Q := Nat.le_floor hrP
  have hQP : (Q : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hlogQP : Real.log Q ≤ Real.log P := Real.log_le_log hQ0 hQP
  have hstrip : ∀ x : ℝ, 1 - a / Real.log P ≤ x → 1 - cL / Real.log (Q : ℝ) ≤ x := by
    intro x hx
    have h1 : a / Real.log P ≤ cL / Real.log P := div_le_div_of_nonneg_right haL hlogP.le
    have h2 : cL / Real.log P ≤ cL / Real.log (Q : ℝ) :=
      div_le_div_of_nonneg_left hcL.le hlogQ hlogQP
    linarith
  have hlift := hL Q hQ2 q r hqQ hrQ ψ χ hψ1 hχ1 σ β hσ1.le hβ1.le hσz hβz
    (hstrip σ hσa) (hstrip β hβa)
  have : NeZero (q * r) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  obtain ⟨hqr, hheq⟩ := pu_primitive_eq_of_lift_eq q r (q * r) ψ χ hψp hχp _ _ hlift
  refine ⟨hqr, hheq, ?_⟩
  subst hqr
  have hψχ : ψ = χ := eq_of_heq hheq
  subst hψχ
  have hbσ := pu_box hcP hP hqP ha.le haP hσa
  have hbβ := pu_box hcP hP hqP ha.le haP hβa
  have hlogBt : 0 < Real.log (Bt q 0) := by linarith [one_le_log_Bt (N := q) 0]
  have him : |((0 : ℝ))| ≤ cP / Real.log (Bt q 0) := by
    rw [abs_zero]; exact (div_pos hcP hlogBt).le
  have hEq := hPg q ψ hψ1 (σ : ℂ) (β : ℂ) hσz hβz
    (by rw [Complex.ofReal_re]; exact hbσ) (by rw [Complex.ofReal_im]; exact him)
    (by rw [Complex.ofReal_re]; exact hbβ) (by rw [Complex.ofReal_im]; exact him)
  exact_mod_cast hEq

/-- LEAF: P0082 page 358 display 9, uniqueness of the exceptional pair, in the residual case
where the given exceptional modulus `r` exceeds `P`. HARD. A real nontrivial primitive
character of modulus `r > P` with a zero in the strip `[1 - a / log P, 1)` leaves no zero in
that strip for any primitive character of modulus at most `P`.  The paper's selection only
uses `r ≤ P`, the case proved in `exceptional_pair_unique_bounded`. -/
theorem leaf_exceptional_pair_unique_large_modulus :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ), P < (r : ℝ) →
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
          1 - a / Real.log P ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
              1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
                ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → ψ.LFunction σ = 0 → False := by
  sorry

/-- Assembly of `leaf_exceptional_pair_unique` from the proved bounded case and the residual
leaf, with the smaller of the two widths. -/
theorem leaf_exceptional_pair_unique_split :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
          1 - a / Real.log P ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
              1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
                ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → ψ.LFunction σ = 0 →
                  q = r ∧ HEq ψ χ ∧ σ = β := by
  obtain ⟨a₁, ha₁, H₁⟩ := exceptional_pair_unique_bounded
  obtain ⟨a₂, ha₂, H₂⟩ := leaf_exceptional_pair_unique_large_modulus
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, ?_⟩
  intro P hP r hr χ β hχp hχ2 hχ1 hβ0 hβa hβ1 hβz q hq ψ h1q hqP hψp σ hσa hσ1 hσz
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hw : ∀ b : ℝ, min a₁ a₂ ≤ b → ∀ x : ℝ, 1 - min a₁ a₂ / Real.log P ≤ x →
      1 - b / Real.log P ≤ x := by
    intro b hb x hx
    have := div_le_div_of_nonneg_right hb hlogP.le
    linarith
  by_cases hrP : (r : ℝ) ≤ P
  · exact H₁ P hP r hr χ β hrP hχp hχ2 hχ1 hβ0 (hw a₁ (min_le_left _ _) β hβa) hβ1 hβz
      q hq ψ h1q hqP hψp σ (hw a₁ (min_le_left _ _) σ hσa) hσ1 hσz
  · exact (H₂ P hP r hr χ β (not_le.mp hrP) hχp hχ2 hχ1 hβ0
      (hw a₂ (min_le_right _ _) β hβa) hβ1 hβz
      q hq ψ h1q hqP hψp σ (hw a₂ (min_le_right _ _) σ hσa) hσ1 hσz).elim

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
