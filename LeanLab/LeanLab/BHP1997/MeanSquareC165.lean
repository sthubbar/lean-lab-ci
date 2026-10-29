/-
P0069, Lemma 1, pages 11 and 12. The two cited analytic statements
are separate from their elementary cardinal consequence.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.Thm4Statement

namespace LeanLab.BHP1997.MeanSquareC165
open Classical Complex

/-- Page 11, the coefficient energy G in Lemma 1, display 3.3. -/
noncomputable def energy (a : ℕ → ℂ) (c1 c2 F : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
      (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F), ‖a n‖ ^ 2 / (n : ℝ)

/-- Page 11, Lemma 1, display 3.3. CITED and unproved.
Montgomery reference 21, Lemma 1.4 and Theorem 6.4, as cited on page 12.
This paper Prop requires Claude review before merge. -/
def Lemma1MeanSquare : Prop :=
  ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
    ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
          C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F

/-- Page 11, Lemma 1, display 3.4. CITED and unproved.
The large value estimate uses Montgomery reference 21, Theorem 8.3,
and Huxley reference 14, Section 2, as cited on page 12.
This paper Prop requires Claude review before merge. -/
def Lemma1LargeValues : Prop :=
  ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
    ∀ x F T V : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
      0 < V → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
        (S.card : ℝ) ≤ C * Real.log x ^ 2 *
          (energy a c1 c2 F * F / V ^ 2 +
            energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)

/-- Page 11, the elementary cardinal consequence of a mean square
bound. Mathlib card_nsmul_le_sum supplies the finite sum comparison.
This weak consequence does not assert the stronger display 3.4. -/
theorem cardinal_of_square_sum {α : Type*} (S : Finset α) (f : α → ℂ)
    {V H : ℝ} (hV : 0 < V) (hpoint : ∀ p ∈ S, V ≤ ‖f p‖)
    (hmean : (∑ p ∈ S, ‖f p‖ ^ 2) ≤ H) : (S.card : ℝ) ≤ H / V ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hV)).mpr
  have hs := Finset.card_nsmul_le_sum S (fun p => ‖f p‖ ^ 2) (V ^ 2)
    (fun p hp => pow_le_pow_left₀ hV.le (hpoint p hp) 2)
  have hcard : (S.card : ℝ) * V ^ 2 ≤ ∑ p ∈ S, ‖f p‖ ^ 2 := by
    simpa only [nsmul_eq_mul] using hs
  exact hcard.trans hmean

/-- Pages 11 and 12, display 3.3 implies a weak large value estimate.
CONDITIONAL on Lemma1MeanSquare. Display 3.4 remains an independent
cited analytic input. -/
theorem weak_large_values (h1 : Lemma1MeanSquare) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T V : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        0 < V → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
          (S.card : ℝ) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F / V ^ 2 := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C, hC, hmean⟩ := h1 B c1 c2 hc1 hc2
  refine ⟨C, hC, ?_⟩
  intro x F T V q S a hcoeff hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  exact cardinal_of_square_sum S
    (fun p => Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)) hV hpoint
    (hmean x F T q S a hcoeff hx hF hFx hT hTx hq hqx hspace htimes)

/-- Page 11, a comparison of the two bracket factors at G equal to 1,
qT equal to F squared and V squared equal to F. The weak mean square
factor is F plus 1. The large value factor is 2. This records the loss. -/
theorem chebyshev_loss {F : ℝ} (hF : 0 < F) :
    (F ^ 2 + F) / F = F + 1 ∧ F / F + F * F ^ 2 / F ^ 3 = 2 := by
  constructor <;> field_simp <;> ring

end LeanLab.BHP1997.MeanSquareC165
