/- AI wrote this Lean code for CODEX task148.
Recovered from the recorded write commands. Fresh checks are required.
Journal Lemma 8, large conductors. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp148a
namespace LeanLab.BS2022GRH.Decomp148c
open Real Finset Classical ChenThresholdGRH Decomp148a
/-- LEAF. One dyadic block, display 15 p. 1225.
CITED source is Iwaniec and Kowalski, Analytic Number Theory, Theorem 7.13.
The lab's bilinear_large_sieve is a starting point. -/
theorem dyadic_block (c : ℕ → ℂ) (X Y Z R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    (∑ r ∈ (Ico 3 ⌈2 * R⌉₊).filter (fun r : ℕ => R ≤ (r : ℝ)),
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R := by
  sorry
/-- LEAF. Dyadic summation, display 16 p. 1226.
Use dyadic_block and Lemma 5. CITED weighted totient input is Ramare 2019 Theorem 3.1. -/
theorem large_conductors (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hDX : D < √(X * Y))
    (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) (hbal : √(X * Y) / D ≤ D₀) (ha : Even a) :
    largeMass c X Y Z D D₀ a ≤ largeBound X Y D D₀ := by
  sorry
/-- Large-conductor step at the chosen cutoff. OPEN through large_conductors. -/
theorem large_at_cutoff (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hDX : D < √(X * Y)) (hcut : 1 < cutoff Y)
    (hcutD : cutoff Y ≤ min D (√Z)) (hbal : √(X * Y) / D ≤ cutoff Y) (ha : Even a) :
    largeMass c X Y Z D (cutoff Y) a ≤ largeBound X Y D (cutoff Y) :=
  large_conductors c X Y Z D (cutoff Y) a hc hX hY hZ hZY hD hDX hcut
    (le_trans hcutD (min_le_left _ _)) hbal ha
end LeanLab.BS2022GRH.Decomp148c
#print axioms LeanLab.BS2022GRH.Decomp148c.dyadic_block
#print axioms LeanLab.BS2022GRH.Decomp148c.large_conductors
#print axioms LeanLab.BS2022GRH.Decomp148c.large_at_cutoff
