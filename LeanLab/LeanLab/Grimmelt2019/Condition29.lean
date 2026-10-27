/-
AI wrote this Lean code for CODEX task03.
P0074, page 12, condition 29, and page 13, differencing the character sums.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Characters

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Condition 29 on an arbitrary finite support, with its exact integer count. -/
def PrefixCharacterBound (S : Finset ℤ) (q : ℕ) (ω : ℤ → ℝ) (cω E : ℝ) : Prop :=
  ∀ t : ℤ, ∀ χ : DirichletCharacter ℂ q,
    ‖∑ m ∈ S.filter (fun m => m ≤ t),
      ((ω m : ℂ) * χ (m : ZMod q) - if χ = 1 then (cω : ℂ) else 0)‖ ≤ E

/-- Two prefix estimates give a bound for the interval between them. -/
theorem character_interval_bound {S : Finset ℤ} {q : ℕ} {ω : ℤ → ℝ} {cω E : ℝ}
    (h : PrefixCharacterBound S q ω cω E) (a b : ℤ) (hab : a ≤ b) :
    CharacterEquidist (S.filter (fun m => a ≤ m ∧ m < b)) q ω
      (cω * ((S.filter (fun m => a ≤ m ∧ m < b)).card : ℝ)) (2 * E) := by
  classical
  intro χ
  let f : ℤ → ℂ := fun m =>
    (ω m : ℂ) * χ (m : ZMod q) - if χ = 1 then (cω : ℂ) else 0
  have hsplit : (∑ m ∈ S.filter (fun m => a ≤ m ∧ m < b), f m) =
      (∑ m ∈ S.filter (fun m => m ≤ b - 1), f m) -
        ∑ m ∈ S.filter (fun m => m ≤ a - 1), f m := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hma : a ≤ m
    · by_cases hmb : m < b
      · simp [hma, hmb, show m ≤ b - 1 by omega, show ¬ m ≤ a - 1 by omega]
      · simp [hma, hmb, show ¬ m ≤ b - 1 by omega, show ¬ m ≤ a - 1 by omega]
    · simp [hma, show m ≤ a - 1 by omega, show m ≤ b - 1 by omega]
  have hcenter : (∑ m ∈ S.filter (fun m => a ≤ m ∧ m < b), f m) =
      (∑ m ∈ S.filter (fun m => a ≤ m ∧ m < b), (ω m : ℂ) * χ (m : ZMod q)) -
        if χ = 1 then ((cω * ((S.filter (fun m => a ≤ m ∧ m < b)).card : ℝ) : ℝ) : ℂ) else 0 := by
    simp only [f, Finset.sum_sub_distrib]
    by_cases hc : χ = 1 <;> simp [hc, mul_comm]
  rw [← hcenter, hsplit]
  exact (norm_sub_le _ _).trans (by linarith [h (b - 1) χ, h (a - 1) χ])

/-- Moving the principal center by at most D increases the error by at most D. -/
theorem CharacterEquidist.change_center {W : Finset ℤ} {q : ℕ} {ω : ℤ → ℝ}
    {M M' E D : ℝ} (h : CharacterEquidist W q ω M E) (hD : |M - M'| ≤ D)
    (hD0 : 0 ≤ D) : CharacterEquidist W q ω M' (E + D) := by
  classical
  intro χ
  by_cases hc : χ = 1
  · have heq : (∑ m ∈ W, (ω m : ℂ) * χ (m : ZMod q)) - (M' : ℂ) =
        ((∑ m ∈ W, (ω m : ℂ) * χ (m : ZMod q)) - (M : ℂ)) +
          ((M : ℂ) - (M' : ℂ)) := by ring
    simp only [if_pos hc] at h ⊢
    rw [heq]
    apply (norm_add_le _ _).trans
    have hn : ‖(M : ℂ) - (M' : ℂ)‖ ≤ D := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hD
    exact add_le_add (by simpa [hc] using h χ) hn
  · simpa only [if_neg hc] using le_trans (h χ) (le_add_of_nonneg_right hD0)

#print axioms character_interval_bound
#print axioms CharacterEquidist.change_center
end LeanLab.Grimmelt2019.MainTerm
