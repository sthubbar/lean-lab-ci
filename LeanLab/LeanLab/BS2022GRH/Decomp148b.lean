/- AI wrote this Lean code for CODEX task148.
Recovered from the recorded write commands. Fresh checks are required.
Journal Lemma 8, small conductors. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp148a
namespace LeanLab.BS2022GRH.Decomp148b
open Real Finset Classical ChenThresholdGRH Decomp148a
/-- LEAF. GRH prime-character estimate, p. 1224 before display 13.
CITED input is Ernvall-Hytonen and Palojarvi 2022 Theorem 1 through Lemma 3.
The two endpoint corrections account for prime endpoints. -/
theorem prime_character_bound (hG : GRH) (Y Z : ℝ) (r : ℕ)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hr : 3 ≤ r) (hrZ : (r : ℝ) ≤ √Z)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ‖∑ p ∈ pRange Y Z, χ p‖ ≤ 2 * r.totient * (1 + qG Y * √Y * log Y) := by
  sorry
/-- LEAF. Small conductors, display 13 p. 1224.
Use prime_character_bound, Robin's Lemma 4 and the weighted totient estimate of Lemma 5.
CITED inputs are Robin 1983 Theorem 11 and Ramare 2019 Theorem 3.1. -/
theorem small_conductors (hG : GRH) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D)
    (hD₀Z : D₀ ≤ √Z) (hbal : √(X * Y) / D ≤ D₀) (ha : Even a) :
    smallMass c X Y Z D D₀ a ≤ smallBound X Y D D₀ := by
  sorry
/-- Small-conductor step at the chosen cutoff. OPEN through small_conductors. -/
theorem small_at_cutoff (hG : GRH) (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hcut : 1 < cutoff Y)
    (hcutD : cutoff Y ≤ min D (√Z)) (hbal : √(X * Y) / D ≤ cutoff Y) (ha : Even a) :
    smallMass c X Y Z D (cutoff Y) a ≤ smallBound X Y D (cutoff Y) :=
  small_conductors hG c X Y Z D (cutoff Y) a hc hX hY hZ hZY hD hcut
    (le_trans hcutD (min_le_left _ _)) (le_trans hcutD (min_le_right _ _)) hbal ha
end LeanLab.BS2022GRH.Decomp148b
#print axioms LeanLab.BS2022GRH.Decomp148b.prime_character_bound
#print axioms LeanLab.BS2022GRH.Decomp148b.small_conductors
#print axioms LeanLab.BS2022GRH.Decomp148b.small_at_cutoff
