import LeanLab.ExceptionalSet.UpJ200.DecompJ200
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanLab.PNTPort.DirichletZF.RealZero
import LeanLab.PNTPort.DirichletZF.SiegelSigns

/-!
P0082 pages 358 and 362 to 364. Shared exceptional conductor selection.
Source: https://doi.org/10.5802/aif.1621
The original pointwise leaf stays open for reviewer repointing.
The case leaves use the same selected conductor. They assert no exceptional count.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Real Finset
/-- The sum of the explicit positive envelopes for Gamma1 and Gamma2.
P0082 page 359 displays 14 and 15. The implicit constants belong in the
pointwise estimate. The integer m is allowed to have either parity. -/
noncomputable def divisorError (r : ℕ) (P : ℝ) (m : ℤ) : ℝ :=
  (r : ℝ) / P *
    ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
      (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) +
  (r : ℝ) * ∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0

end LeanLab.ExceptionalSet.UpJ200.Decomp527a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b
open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- P0082 page 358 display 9. Either there is no real zero in the
exceptional interval or one primitive real character and one zero account
for every real zero there. The upper endpoint one is excluded to avoid
the pole of a principal L function. -/
def SelectedRealZero (a P : ℝ) (r : ℕ) : Prop :=
  (r = 1 ∧ ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
    1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
      ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → χ.LFunction σ ≠ 0) ∨
  ∃ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
    χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
    0 < β ∧ 1 - a / Real.log P ≤ β ∧ β < 1 ∧ χ.LFunction β = 0 ∧
    ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
      1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
        ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → ψ.LFunction σ = 0 →
          q = r ∧ HEq ψ χ ∧ σ = β

/-- LEAF: P0082 page 358 display 9 and the paragraph before display 10.
Existence and uniqueness of the exceptional real character. This contains
no major arc lower estimate and no counting statement. -/
theorem leaf_selected_real_zero :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ P ∧ SelectedRealZero a P r := by
  have primitive_eq_of_lift_eq (r q M : ℕ) [NeZero M]
      (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ q)
      (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hr : r ∣ M) (hq : q ∣ M)
      (heq : DirichletCharacter.changeLevel hr χ = DirichletCharacter.changeLevel hq ψ) :
      r = q ∧ HEq χ ψ := by
    have hlevel : r = q := by
      calc
        r = χ.conductor := hχ.symm
        _ = (DirichletCharacter.changeLevel hr χ).conductor :=
          (DirichletCharacter.conductor_changeLevel χ hr).symm
        _ = (DirichletCharacter.changeLevel hq ψ).conductor := congrArg _ heq
        _ = ψ.conductor := DirichletCharacter.conductor_changeLevel ψ hq
        _ = q := hψ
    subst q
    exact ⟨rfl, heq_of_eq (DirichletCharacter.changeLevel_injective hr heq)⟩

  have selected_zero_pos (a P β : ℝ) (ha : a ≤ 1 / 4) (hP : 2 ≤ P)
      (hβ : 1 - a / Real.log P ≤ β) : 0 < β := by
    have hlog2 : (1 / 4 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
    have hlogP0 : 0 < Real.log P := by linarith
    have hlt : a / Real.log P < 1 := (div_lt_one hlogP0).mpr (by linarith)
    linarith

  have primitive_principal_nonvanishing (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (β : ℝ)
      (hβ0 : 0 < β) (hβ1 : β < 1) : χ = 1 → χ.LFunction β ≠ 0 := by
    intro heq hz
    have hq : q = 1 := by
      have hc : χ.conductor = q := hp
      rw [heq, DirichletCharacter.conductor_one] at hc
      exact hc.symm
    subst q
    have hneg := (LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg hβ0 hβ1).2
    rw [heq, DirichletCharacter.LFunction_modOne_eq] at hz
    rw [hz] at hneg
    simp at hneg

  have log_product_scale (M : ℕ) [NeZero M] (P : ℝ) (hP : 2 ≤ P)
      (hM : (M : ℝ) ≤ P ^ 2) :
      Real.log (LeanLab.PNTPort.DirichletZF.Bt M 0) ≤ (Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2) * Real.log P := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
    have h6 : (0 : ℝ) < 6 * LeanLab.PNTPort.DirichletZF.Z := by have := LeanLab.PNTPort.DirichletZF.one_le_Z; linarith
    have hL : 0 ≤ Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) := Real.log_nonneg (by have := LeanLab.PNTPort.DirichletZF.one_le_Z; linarith)
    have hlogM : Real.log (M : ℝ) ≤ 2 * Real.log P := by
      have h := Real.log_le_log hM0 hM
      rwa [Real.log_pow] at h
    have hconstant : Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) ≤ Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 * Real.log P := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlogP hL
    have hb : LeanLab.PNTPort.DirichletZF.Bt M 0 = (6 * LeanLab.PNTPort.DirichletZF.Z) * M := by unfold LeanLab.PNTPort.DirichletZF.Bt; simp; ring
    rw [hb, Real.log_mul h6.ne' hM0.ne']
    nlinarith only [hconstant, hlogM]

  have selection_strip_inside (c a P β : ℝ) (hc : 0 < c) (ha0 : 0 ≤ a)
      (ha : a ≤ c / (2 * (Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2)))
      (M : ℕ) [NeZero M] (hP : 2 ≤ P) (hM : (M : ℝ) ≤ P ^ 2)
      (hβ : 1 - a / Real.log P ≤ β) :
      1 - c / Real.log (LeanLab.PNTPort.DirichletZF.Bt M 0) < β := by
    have hL : 0 ≤ Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) := Real.log_nonneg (by have := LeanLab.PNTPort.DirichletZF.one_le_Z; linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK : 0 < Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2 := by positivity
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    have hlogM : 0 < Real.log (LeanLab.PNTPort.DirichletZF.Bt M 0) := by linarith [LeanLab.PNTPort.DirichletZF.one_le_log_Bt (N := M) 0]
    have hbound := log_product_scale M P hP hM
    have hak : a * (Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2) ≤ c / 2 := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * (Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2))).mp ha
      nlinarith only [h]
    have hmul := mul_le_mul_of_nonneg_left hbound ha0
    have hmul' := mul_le_mul_of_nonneg_right hak hlogP.le
    have hdiv : a / Real.log P < c / Real.log (LeanLab.PNTPort.DirichletZF.Bt M 0) := by
      rw [div_lt_div_iff₀ hlogP hlogM]
      nlinarith only [hmul, hmul', mul_pos hc hlogP]
    linarith

  classical
  obtain ⟨c, c', hc, hc', H⟩ := LeanLab.PNTPort.DirichletZF.zero_free_region_real
  let K := Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) / Real.log 2 + 2
  have hL : 0 ≤ Real.log (6 * LeanLab.PNTPort.DirichletZF.Z) := Real.log_nonneg (by have := LeanLab.PNTPort.DirichletZF.one_le_Z; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  let a := min (c / (2 * K)) (1 / 4)
  have ha : 0 < a := lt_min (div_pos hc (by positivity)) (by norm_num)
  have ha4 : a ≤ 1 / 4 := min_le_right _ _
  have hac : a ≤ c / (2 * K) := min_le_left _ _
  refine ⟨a, ha, ?_⟩
  intro P hP
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hpositive (β : ℝ) (hβ : 1 - a / Real.log P ≤ β) : 0 < β :=
    selected_zero_pos a P β ha4 hP hβ
  have hbox (M : ℕ) [NeZero M] (hM : (M : ℝ) ≤ P ^ 2)
      (β : ℝ) (hβ : 1 - a / Real.log P ≤ β) :
      1 - c / Real.log (LeanLab.PNTPort.DirichletZF.Bt M 0) < β :=
    selection_strip_inside c a P β hc ha.le hac M hP hM hβ
  by_cases hfree : ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
        ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → χ.LFunction σ ≠ 0
  · exact ⟨1, le_rfl, by exact_mod_cast hP1, Or.inl ⟨rfl, hfree⟩⟩
  push Not at hfree
  obtain ⟨r, hrzero, χ, hr1, hrP, hp, β, hβ, hβ1, hz⟩ := hfree
  letI : NeZero r := hrzero
  have hχ : χ ≠ 1 := fun heq => primitive_principal_nonvanishing r χ hp β (hpositive β hβ) hβ1 heq hz
  have hβbox := hbox r (hrP.trans hP2) β hβ
  have hreal : χ ^ 2 = 1 := by
    rcases (H r χ hχ).1 (β : ℂ) hz with hleft | hright
    · simp only [Complex.ofReal_re, Complex.ofReal_im] at hleft
      exact False.elim (not_lt_of_ge hleft hβbox)
    · exact hright.2.2.1
  refine ⟨r, hr1, hrP, Or.inr ⟨hrzero, χ, β, hp, hreal, hχ,
    hpositive β hβ, hβ, hβ1, hz, ?_⟩⟩
  intro q hqzero ψ hq1 hqP hψ σ hσ hσ1 hσzero
  letI : NeZero q := hqzero
  have hψne : ψ ≠ 1 :=
    fun heq => primitive_principal_nonvanishing q ψ hψ σ (hpositive σ hσ) hσ1 heq hσzero
  let M := q * r
  haveI : NeZero M := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  have hM : (M : ℝ) ≤ P ^ 2 := by
    dsimp [M]
    push_cast
    nlinarith only [mul_le_mul hqP hrP (Nat.cast_nonneg r) hP0.le]
  let dq : q ∣ M := Nat.dvd_mul_right q r
  let dr : r ∣ M := Nat.dvd_mul_left r q
  have hψlift : DirichletCharacter.changeLevel dq ψ ≠ 1 :=
    fun heq => hψne ((DirichletCharacter.changeLevel_eq_one_iff dq).mp heq)
  have hχlift : DirichletCharacter.changeLevel dr χ ≠ 1 :=
    fun heq => hχ ((DirichletCharacter.changeLevel_eq_one_iff dr).mp heq)
  have hσlift : (DirichletCharacter.changeLevel dq ψ).LFunction σ = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel dq ψ (Or.inl hψne), hσzero, zero_mul]
  have hβlift : (DirichletCharacter.changeLevel dr χ).LFunction β = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel dr χ (Or.inl hχ), hz, zero_mul]
  have hlogM : 0 < Real.log (LeanLab.PNTPort.DirichletZF.Bt M 0) := by linarith [LeanLab.PNTPort.DirichletZF.one_le_log_Bt (N := M) 0]
  obtain ⟨hlifts, hzeros⟩ := (H M (DirichletCharacter.changeLevel dq ψ) hψlift).2
    (DirichletCharacter.changeLevel dr χ) hχlift (σ : ℂ) (β : ℂ) hσlift hβlift
    (by simpa only [Complex.ofReal_re] using (hbox M hM σ hσ).le)
    (by simp only [Complex.ofReal_im, abs_zero]; positivity)
    (by simpa only [Complex.ofReal_re] using (hbox M hM β hβ).le)
    (by simp only [Complex.ofReal_im, abs_zero]; positivity)
  obtain ⟨hlevels, hcharacters⟩ := primitive_eq_of_lift_eq q r M ψ χ hψ hp dq dr hlifts
  exact ⟨hlevels, hcharacters, Complex.ofReal_injective hzeros⟩

/-- P0082 page 358. A selected exceptional modulus has the exact
primitive real character alternative used by the original leaf.
CONDITIONAL ON the explicit SelectedRealZero premise. -/
theorem selected_shape (a P : ℝ) (r : ℕ) (h : SelectedRealZero a P r) :
    r = 1 ∨ ∃ (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 := by
  rcases h with h | ⟨hr, χ, β, hp, hreal, hne, _⟩
  · exact Or.inl h.1
  · exact Or.inr ⟨hr, χ, hp, hreal, hne⟩

/-- LEAF: P0082 page 362 case i and page 358 Lemma 2.
Only the absent exceptional character case is included. -/
theorem leaf_absent_selected (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- LEAF: P0082 page 363 case ii a after display 20.
Only the coprime exceptional conductor case is included. -/
theorem leaf_coprime_selected (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n + j) r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- LEAF: P0082 page 363 case ii b and display 21.
Only the nonempty prime product case is included. -/
theorem leaf_prime_product_selected (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- LEAF: P0082 page 364 case ii d and page 358 display 10.
Only the empty prime product with small conductor case is included. -/
theorem leaf_near_zero_selected (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + j) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- P0082 pages 362 to 364 Lemma 7. One shared selection and the four
strictly smaller case leaves imply the exact original pointwise statement.
CONDITIONAL ON the five open analytic leaves in this file. -/
theorem pointwise_major_character_from_selected_cases (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            (r = 1 ∨ ∃ (_ : NeZero r) (χ : DirichletCharacter ℂ r),
              χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              let Y := (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)
              (r = 1 → c * F γ N ≤ Y) ∧
              (r ≠ 1 → Int.gcd (nu γ n + j) r = 1 → c * F γ N ≤ Y) ∧
              (1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                  c * F γ N ≤ Y) ∧
              (1 < Int.gcd (nu γ n + j) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                  c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ Y) := by
  obtain ⟨a, hapos, hselect⟩ := leaf_selected_real_zero
  obtain ⟨δa, hδa, ha⟩ := leaf_absent_selected γ h1 h2 a hapos
  obtain ⟨δb, hδb, hb⟩ := leaf_coprime_selected γ h1 h2 a hapos
  obtain ⟨δd, hδd, hd⟩ := leaf_prime_product_selected γ h1 h2 a hapos
  obtain ⟨δe, hδe, he⟩ := leaf_near_zero_selected γ h1 h2 a hapos
  refine ⟨min δa (min δb (min δd δe)), lt_min hδa (lt_min hδb (lt_min hδd hδe)), ?_⟩
  intro δ hδ hδsmall
  have hdeltas := lt_min_iff.mp hδsmall
  have hdeltas' := lt_min_iff.mp hdeltas.2
  have hdeltas'' := lt_min_iff.mp hdeltas'.2
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ hdeltas.1
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ hdeltas'.1
  obtain ⟨κd, hκd, hd⟩ := hd δ hδ hdeltas''.1
  obtain ⟨κe, hκe, he⟩ := he δ hδ hdeltas''.2
  refine ⟨min κa (min κb (min κd κe)), lt_min hκa (lt_min hκb (lt_min hκd hκe)), ?_⟩
  intro κ hκ hκsmall
  have hkappas := le_min_iff.mp hκsmall
  have hkappas' := le_min_iff.mp hkappas.2
  have hkappas'' := le_min_iff.mp hkappas'.2
  obtain ⟨ca, Aa, hca, hAa, Na, ha⟩ := ha κ hκ hkappas.1
  obtain ⟨cb, Ab, hcb, hAb, Nb, hb⟩ := hb κ hκ hkappas'.1
  obtain ⟨cd, Ad, hcd, hAd, Nd, hd⟩ := hd κ hκ hkappas''.1
  obtain ⟨ce, Ae, hce, hAe, Ne, he⟩ := he κ hκ hkappas''.2
  let c := min ca (min cb (min cd ce))
  let A := Aa + Ab + Ad + Ae
  have hc : 0 < c := lt_min hca (lt_min hcb (lt_min hcd hce))
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  obtain ⟨Np, hNp⟩ := eventually_atTop.mp (hP.eventually_ge_atTop 2)
  refine ⟨c, A, hc, hA, max Np (max Na (max Nb (max Nd Ne))), ?_⟩
  intro N hN
  have hNs := max_le_iff.mp hN
  have hNs' := max_le_iff.mp hNs.2
  have hNs'' := max_le_iff.mp hNs'.2
  have hNs''' := max_le_iff.mp hNs''.2
  obtain ⟨r, hr, hrP, hs⟩ := hselect _ (hNp N hNs.1)
  refine ⟨r, hr, hrP, selected_shape a _ r hs, ?_⟩
  intro j hj n hn heven hm
  dsimp only
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hP0 : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg hX _
  have hD : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hca' : c ≤ ca := min_le_left _ _
  have hcb' : c ≤ cb := (min_le_right _ _).trans (min_le_left _ _)
  have hcd' : c ≤ cd := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hce' : c ≤ ce := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAa' : Aa ≤ A := by dsimp [A]; linarith
  have hAb' : Ab ≤ A := by dsimp [A]; linarith
  have hAd' : Ad ≤ A := by dsimp [A]; linarith
  have hAe' : Ae ≤ A := by dsimp [A]; linarith
  have transfer (ci Ai w : ℝ) (hw : 0 ≤ w) (hci : c ≤ ci) (hAi : Ai ≤ A)
      (h : ci * F γ N * w ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
        Ai * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)) :
      c * F γ N * w ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
        A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
    have hleft := mul_le_mul_of_nonneg_right hci (mul_nonneg hX hw)
    have hright := mul_le_mul_of_nonneg_right hAi (mul_nonneg hX hD)
    nlinarith only [hleft, hright, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcase
    have hh := ha N hNs'.1 r hr hrP hs j hj n hn heven hm hcase
    simpa only [mul_one] using transfer ca Aa 1 (by norm_num) hca' hAa' (by simpa using hh)
  · intro hcase hgcd
    have hh := hb N hNs''.1 r hr hrP hs j hj n hn heven hm hcase hgcd
    simpa only [mul_one] using transfer cb Ab 1 (by norm_num) hcb' hAb' (by simpa using hh)
  · intro hgcd hprime
    have hh := hd N hNs'''.1 r hr hrP hs j hj n hn heven hm hgcd hprime
    simpa only [mul_one] using transfer cd Ad 1 (by norm_num) hcd' hAd' (by simpa using hh)
  · intro hgcd hprime hsmall
    exact transfer ce Ae _ (Real.rpow_nonneg (Real.exp_pos _).le _) hce' hAe'
      (he N hNs'''.2 r hr hrP hs j hj n hn heven hm hgcd hprime hsmall)
end LeanLab.ExceptionalSet.UpJ200.Decomp559b

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-- P0082 page 358 display 9. Two selected conductors in the same
bounded range and real interval are equal.
CONDITIONAL ON the two explicit SelectedRealZero premises. -/
theorem selected_conductor_unique656 (a P : ℝ) (r s : ℕ)
    (hr : 1 ≤ r) (hrP : (r : ℝ) ≤ P) (hs : 1 ≤ s) (hsP : (s : ℝ) ≤ P)
    (h : SelectedRealZero a P r) (h' : SelectedRealZero a P s) : r = s := by
  rcases h with ⟨hrone, hfree⟩ | ⟨hrzero, χ, β, hχ, hχ2, hχne, hβpos, hβlo, hβone, hβzero, huniq⟩
  · rcases h' with ⟨hsone, _⟩ | ⟨hszero, ψ, σ, hψ, _, _, _, hσlo, hσone, hσzero, _⟩
    · exact hrone.trans hsone.symm
    · exact False.elim (hfree s hszero ψ hs hsP hψ σ hσlo hσone hσzero)
  · rcases h' with ⟨_, hfree⟩ | ⟨hszero, ψ, σ, hψ, _, _, _, hσlo, hσone, hσzero, _⟩
    · exact False.elim (hfree r hrzero χ hr hrP hχ β hβlo hβone hβzero)
    · exact (huniq s hszero ψ hs hsP hψ σ hσlo hσone hσzero).1.symm

end LeanLab.ExceptionalSet.UpJ200.Decomp559b

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (R1 Sp eC majorArcs)

/-- P0082 page 357 display 7. Reflection of the major arcs about one half
conjugates the integrand at an integer frequency. The coefficient is real.
This symmetry identity also holds for the extended real cutoff parameters. -/
theorem R1_im_eq_zero656 (P X : ℝ) (m : ℤ) : (R1 P X m).im = 0 := by
  classical
  have heconj (t : ℝ) : (starRingEnd ℂ) (eC t) = eC (-t) := by
    unfold eC
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, map_ofNat]
  have heperiod (t : ℝ) (k : ℤ) : eC (t + (k : ℝ)) = eC t := by
    unfold eC
    rw [show (2 * π * Complex.I * ((t + (k : ℝ) : ℝ) : ℂ)) =
      2 * π * Complex.I * t + k * (2 * π * Complex.I) by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hereflect (t : ℝ) (k : ℤ) : eC ((k : ℝ) - t) = (starRingEnd ℂ) (eC t) := by
    rw [heconj, show (k : ℝ) - t = -t + k by ring, heperiod]
  have hs (x : ℝ) : Sp P X (1 - x) = (starRingEnd ℂ) (Sp P X x) := by
    simp only [Sp, map_sum, map_mul, Complex.conj_ofReal]
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    rw [show (1 - x) * (p : ℝ) = (p : ℝ) - x * p by ring]
    simpa only [Int.cast_natCast] using hereflect (x * p) (p : ℤ)
  have hm (x : ℝ) : eC (-((1 - x) * m)) = (starRingEnd ℂ) (eC (-(x * m))) := by
    rw [show -((1 - x) * (m : ℝ)) = ((-m : ℤ) : ℝ) - (-(x * m)) by push_cast; ring]
    exact hereflect (-(x * m)) (-m)
  have hstep (x : ℝ) (hx : x ∈ majorArcs P X) : 1 - x ∈ majorArcs P X := by
    rcases hx with ⟨q, a, hq1, hqP, hcop, hdist⟩
    refine ⟨q, (q : ℤ) - a, hq1, hqP, ?_, ?_⟩
    · simpa only [Int.gcd_self_sub_left] using hcop
    · have heq : (q : ℝ) * (1 - x) - (((q : ℤ) - a : ℤ) : ℝ) =
          -((q : ℝ) * x - a) := by push_cast; ring
      simpa only [heq, abs_neg] using hdist
  let A := majorArcs P X ∩ Icc (0 : ℝ) 1
  let f := fun x : ℝ => Sp P X x ^ 2 * eC (-(x * m))
  have hA : MeasurableSet A := by dsimp [A, majorArcs]; measurability
  have hmem (x : ℝ) : 1 - x ∈ A ↔ x ∈ A := by
    constructor
    · rintro ⟨hmajor, h0, h1⟩
      refine ⟨?_, by linarith, by linarith⟩
      simpa using hstep (1 - x) hmajor
    · rintro ⟨hmajor, h0, h1⟩
      exact ⟨hstep x hmajor, by linarith, by linarith⟩
  have hf (x : ℝ) : f (1 - x) = (starRingEnd ℂ) (f x) := by
    simp only [f, hs, hm, map_mul, map_pow]
  have hreflect (x : ℝ) : A.indicator f (1 - x) = (starRingEnd ℂ) (A.indicator f x) := by
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).mpr hx), hf]
    · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hmem x).mp hx), map_zero]
  have hi := integral_sub_left_eq_self (A.indicator f) volume (1 : ℝ)
  simp_rw [hreflect] at hi
  rw [integral_conj, integral_indicator hA] at hi
  change (starRingEnd ℂ) (R1 P X m) = R1 P X m at hi
  have him := congrArg Complex.im hi
  simp only [Complex.conj_im] at him
  linarith

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
