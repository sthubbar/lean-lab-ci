import LeanLab.Zhao2025.DecompJ1123

/-!
U-1619 audit of Zhao2025/DecompJ1123 `maynard_2013_bound`, audit defect filed 20261105T0544Z.
AI wrote this Lean code. Binary Goldbach is open.

The leaf has constant exactly 2 with no epsilon. Zhao (1.16) has 2 + epsilon with threshold
depending on epsilon, and that is all `leaf2_low` needs. Not refuted. By hand, the constant 2 form
at exponent 5 cannot be reached by known methods: with a real exceptional zero 1 - d and a
nonresidue class, the count is (Li(X) + Li(X^(1-d)))/phi(q) up to the other zeros, and
Li(X) exceeds X/log X by about X/log^2 X, so the leaf would exclude d = o(1/log^2 q).
So the leaf is a QUESTION with a REPAIR, not FALSE.

Proved here: the repaired form is implied by the old one, and it supplies `leaf2_low` verbatim.
-/

namespace LeanLab.Zhao2025.Audit1619
open LeanLab.Zhao2025.Task56 LeanLab.Zhao2025.Task1123

/-- The old leaf, verbatim. -/
def OldMaynard : Prop :=
  ∀ theta : ℝ, 5 ≤ theta → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        2 * (q : ℝ) ^ theta / ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta))

/-- The repaired leaf: Zhao (1.16) upper half, threshold after epsilon. -/
def RepairedMaynard : Prop :=
  ∀ theta : ℝ, 5 ≤ theta → ∀ epsilon : ℝ, 0 < epsilon → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        (2 + epsilon) * (q : ℝ) ^ theta / ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta))

/-- The repair is a true weakening. -/
theorem repaired_of_old (h : OldMaynard) : RepairedMaynard := by
  intro theta hth epsilon heps
  obtain ⟨Q, hQ⟩ := h theta hth
  refine ⟨max Q 2, fun q hq hq1 a ha1 haq hcop => ?_⟩
  have hq2 : 2 ≤ q := le_trans (le_max_right Q 2) hq
  have h1 := hQ q (le_trans (le_max_left Q 2) hq) hq1 a ha1 haq hcop
  have h2 := scaling_term_nonneg q hq2 theta hth
  have h3 := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ 2 + epsilon) h2
  calc _ ≤ _ := h1
    _ = 2 * ((q : ℝ) ^ theta / ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta))) := by ring
    _ ≤ _ := h3
    _ = _ := by ring

/-- The parent `leaf2_low` statement, character for character, from the repaired leaf. -/
theorem leaf2_low_of_repaired (h : RepairedMaynard) (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ)
    (heps : 0 < epsilon) (_hlow : theta ≤ 1 + 2 / epsilon) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
      ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
        (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
          (2 + epsilon) * (q : ℝ) ^ theta /
            ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) :=
  h theta hth epsilon heps

end LeanLab.Zhao2025.Audit1619

#print axioms LeanLab.Zhao2025.Audit1619.repaired_of_old
#print axioms LeanLab.Zhao2025.Audit1619.leaf2_low_of_repaired
