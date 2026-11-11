import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
The real and nonreal character cases of P0045 preprint page 6.
External results stay cited. Their consequences proved in P0045 stay open.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- P0045 page 6: Davenport Chapter 5, the real primitive conductor classification. -/
def RealPrimitiveStatement481 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∀ a, (χ a).im = 0) →
      r = oddRad131 r ∨ r = 4 * oddRad131 r ∨ r = 8 * oddRad131 r

/-- P0045 page 5: Pintz and Goldfeld and Schinzel, the real zero lower bound. -/
def RealZeroStatement481 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ →
      Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ

/-- P0045 page 6: the denominator in the quoted Iwaniec region. -/
def iwaniecDenom481 (r : ℕ) (t : ℝ) : ℝ :=
  let ℓ := Real.log ((r : ℝ) * (|t| + 2))
  4 * 10 ^ 4 * (Real.log (2 * (oddRad131 r : ℝ)) +
    (ℓ * Real.log (2 * ℓ)) ^ (3 / 4 : ℝ))

/-- P0045 page 6: Iwaniec's zero free region for nonreal primitive characters. -/
def IwaniecStatement481 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∃ a, (χ a).im ≠ 0) → ∀ s : ℂ,
      1 - 1 / iwaniecDenom481 r s.im < s.re → Lfun481 χ s ≠ 0

/-- LEAF. CITED. P0045 page 6, first proof paragraph following display 10.
Davenport Chapter 5 supplies the classification of real primitive conductors. -/
theorem davenport_classification481 : RealPrimitiveStatement481 := by
  sorry

/-- LEAF. CITED. P0045 page 5, the paragraph before Lemma 4.1.
Pintz 1976 and Goldfeld and Schinzel 1975 supply the real zero bound. -/
theorem real_zero_bound481 : RealZeroStatement481 := by
  sorry

/-- LEAF. CITED. P0045 page 6, second proof paragraph following display 10.
Iwaniec 1974 supplies the nonreal character zero free region. -/
theorem iwaniec_zero_free481 : IwaniecStatement481 := by
  sorry

/-- LEAF. OPEN. P0045 page 5 before Lemma 4.1 and page 6, first proof paragraph.
The real zero bound gives the quadratic conductor bound.
Nonreal zeros of real characters also require the classical zero free region.
The primitive principal character is excluded for large X at bounded height. -/
theorem real_exceptional_conductor481 (hzero : RealZeroStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  sorry

/-- LEAF. OPEN. P0045 page 6, last proof paragraph and display 10.
The Iwaniec region gives odd radical growth for nonreal exceptional characters.
This states the weaker quadratic conclusion actually used by the corollary. -/
theorem nonreal_exceptional_radical481 (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∃ a, (z.2.1 a).im ≠ 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  sorry

/-- LEAF. P0045 page 6, first proof paragraph following display 10.
Transfer the conductor lower bound through the three classified possibilities. -/
theorem real_radical_transfer481 {r : ℕ} {Y : ℝ}
    (hclass : r = oddRad131 r ∨ r = 4 * oddRad131 r ∨ r = 8 * oddRad131 r)
    (hY : Y ≤ (r : ℝ)) : Y / 8 ≤ (oddRad131 r : ℝ) := by
  have hr : r ≤ 8 * oddRad131 r := by rcases hclass with h | h | h <;> omega
  have hc : (r : ℝ) ≤ 8 * (oddRad131 r : ℝ) := by exact_mod_cast hr
  linarith

end
end LeanLab.LPZ2007
