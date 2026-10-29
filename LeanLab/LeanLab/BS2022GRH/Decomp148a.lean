/- AI wrote this Lean code for CODEX task148.
Recovered from this run's recorded write commands after execution access failed.
Fresh build, seal and branch checks are required. Goldbach is open. -/
import LeanLab.BS2022GRH.ChenThresholdGRH
import LeanLab.BS2022GRH.CharacterC164
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
namespace LeanLab.BS2022GRH.Decomp148a
open Real Finset Classical ChenThresholdGRH
noncomputable section
/-- Positive integer indices n < X, journal p. 1222. -/
def nRange (X : ℝ) : Finset ℕ := Ico 1 ⌈X⌉₊
/-- Prime indices Z ≤ p < Y, journal p. 1222. -/
def pRange (Y Z : ℝ) : Finset ℕ :=
  (range ⌈Y⌉₊).filter (fun p => p.Prime ∧ Z ≤ (p : ℝ))
/-- The discrepancy inside display 11. -/
def discrepancy (c : ℕ → ℂ) (X Y Z : ℝ) (d b : ℕ) : ℂ :=
  (∑ n ∈ nRange X, ∑ p ∈ (pRange Y Z).filter (fun p => (n * p) % d = b % d), c n)
    - (d.totient : ℂ)⁻¹ *
      ∑ n ∈ nRange X, ∑ p ∈ (pRange Y Z).filter (fun p => Nat.Coprime (n * p) d), c n
/-- Maximum over reduced residues, display 11. -/
def maxDiscrepancy (c : ℕ → ℂ) (X Y Z : ℝ) (d : ℕ) : ℝ :=
  ↑(((range d).filter (fun b => Nat.Coprime b d)).sup
    (fun b => (⟨‖discrepancy c X Y Z d b‖, norm_nonneg _⟩ : NNReal)))
/-- Squarefree moduli with the outer coprimality restriction, display 11. -/
def moduli (D : ℝ) (a : ℤ) : Finset ℕ :=
  (Ico 1 ⌈D⌉₊).filter (fun d => Squarefree d ∧ Nat.Coprime a.natAbs d)
/-- Complete left side of display 11. -/
def bilinear (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ) : ℝ :=
  ∑ d ∈ moduli D a, maxDiscrepancy c X Y Z d
/-- Primitive-character product in display 12. -/
def primitiveTerm (c : ℕ → ℂ) (X Y Z : ℝ) (r s : ℕ) : ℝ :=
  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
    ‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n s), c n * χ n‖ *
    ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), χ p‖
/-- Conductor range, display 12 and p. 1224. -/
def conductors (D : ℝ) (a : ℤ) : Finset ℕ :=
  (Ico 3 ⌈D⌉₊).filter (fun r => Squarefree r ∧ Nat.Coprime a.natAbs r)
/-- Weighted conductor contribution in display 12. -/
def conductorTerm (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ) (r : ℕ) : ℝ :=
  (r.totient : ℝ)⁻¹ * ∑ s ∈ moduli (D / r) a,
    (s.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s
/-- Small-conductor contribution in display 13. -/
def smallMass (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ) : ℝ :=
  ∑ r ∈ (conductors D a).filter (fun r : ℕ => (r : ℝ) ≤ D₀), conductorTerm c X Y Z D a r
/-- Complementary large-conductor contribution, displays 14 and 16. -/
def largeMass (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ) : ℝ :=
  ∑ r ∈ (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ)), conductorTerm c X Y Z D a r
/-- Normalizing factor in displays 17 and 18. -/
def scale (X Y D : ℝ) : ℝ := D * √(X * Y) * log D ^ 2
/-- Chosen splitting point, journal p. 1226. -/
def cutoff (Y : ℝ) : ℝ := (√Y / (2 * log 2 * qG Y * log Y)) ^ (1 / 3 : ℝ)
/-- Right side of display 13. -/
def smallBound (X Y D D₀ : ℝ) : ℝ :=
  Mphi D₀ * Mphi D * D₀ * X * log D ^ 2 *
    (1.3841 * log D / log (log D) + 2 * D₀ + 2 * D₀ * qG Y * √Y * log Y)
/-- Right side of display 16. -/
def largeBound (X Y D D₀ : ℝ) : ℝ :=
  Mphi D / log 2 * log D ^ 2 *
    (4 * D * √(X * Y) + 2 * (√X + √Y) * √(X * Y) + X * Y / D₀)
/-- Common normalized term in displays 17 and 18. -/
def balance (X Y D : ℝ) : ℝ :=
  qG Y ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) *
    (X ^ (1 / 2 : ℝ) * Y ^ (1 / 3 : ℝ) * log Y ^ (1 / 3 : ℝ) / D)
/-- Right side of display 17. -/
def smallCoeff (X Y D : ℝ) : ℝ :=
  2 * Mphi0 Y * Mphi D *
    (balance X Y D + (2 * qG Y * log 2) ^ (-(2 / 3) : ℝ) *
      (X ^ (1 / 2 : ℝ) / (Y ^ (1 / 6 : ℝ) * D * log Y ^ (2 / 3 : ℝ))) +
      0.69205 * (2 * qG Y * log 2) ^ (-(1 / 3) : ℝ) *
      (X ^ (1 / 2 : ℝ) * log D /
        (Y ^ (1 / 3 : ℝ) * D * log (log D) * log Y ^ (1 / 3 : ℝ))))
/-- Right side of display 18. -/
def largeCoeff (X Y D : ℝ) : ℝ :=
  2 * Mphi D * (2 / log 2 + balance X Y D + (√X + √Y) / (D * log 2))
/-- Coefficient m of Lemma 8, split as displays 17 and 18. -/
def mJ (X Y D : ℝ) : ℝ := smallCoeff X Y D + largeCoeff X Y D
/-- Lemma 8, display 11. New paper Prop requiring Claude review.
The unsubscripted maximum is interpreted over reduced residues for each modulus. -/
def Lemma8J : Prop :=
  GRH → ∀ (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ), (∀ n, ‖c n‖ ≤ 1) →
    25 ≤ X → 25 ≤ Y → 25 ≤ Z → Z < Y → 1 < D → D < √(X * Y) →
    √(X * Y) / D ≤ cutoff Y → cutoff Y ≤ min D (√Z) → Even a →
    bilinear c X Y Z D a ≤ mJ X Y D * scale X Y D
/-- LEAF. Orthogonality step, p. 1223 before display 12.
Use DirichletCharacter.sum_char_inv_mul_char_eq and remove the principal character. -/
theorem orthogonality_bound (c : ℕ → ℂ) (X Y Z : ℝ) (d b : ℕ)
    (hd : 0 < d) (hb : Nat.Coprime b d) :
    ‖discrepancy c X Y Z d b‖ ≤ (d.totient : ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
        ‖∑ n ∈ nRange X, c n * χ n‖ * ‖∑ p ∈ pRange Y Z, χ p‖ := by
  exact CharacterC164.error_norm_le (nRange X) (pRange Y Z) c d b hd hb
/-- LEAF. Primitive conductor reduction, display 12 p. 1223.
Use the orthogonality bound and primitiveCharacter_isPrimitive.
Squarefree weights become support conditions. -/
theorem primitive_reduction (c : ℕ → ℂ) (X Y Z D : ℝ) (a : ℤ)
    (hD : 1 < D) (ha : Even a) :
    bilinear c X Y Z D a ≤ ∑ r ∈ conductors D a, conductorTerm c X Y Z D a r := by
  sorry
/-- Split display 12 at the common cutoff. OPEN through primitive_reduction. -/
theorem split_reduction (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
    (hD : 1 < D) (ha : Even a) :
    bilinear c X Y Z D a ≤ smallMass c X Y Z D D₀ a + largeMass c X Y Z D D₀ a := by
  simpa only [smallMass, largeMass, not_le] using
    (primitive_reduction c X Y Z D a hD ha).trans_eq
      (sum_filter_add_sum_filter_not (conductors D a) (fun r : ℕ => (r : ℝ) ≤ D₀)
        (fun r => conductorTerm c X Y Z D a r)).symm
end
end LeanLab.BS2022GRH.Decomp148a
#print axioms LeanLab.BS2022GRH.Decomp148a.orthogonality_bound
#print axioms LeanLab.BS2022GRH.Decomp148a.primitive_reduction
#print axioms LeanLab.BS2022GRH.Decomp148a.split_reduction
