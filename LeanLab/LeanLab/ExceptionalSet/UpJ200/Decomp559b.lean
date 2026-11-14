import LeanLab.ExceptionalSet.UpJ200.DecompJ200
import Mathlib.NumberTheory.LSeries.DirichletContinuation

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
  sorry

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
