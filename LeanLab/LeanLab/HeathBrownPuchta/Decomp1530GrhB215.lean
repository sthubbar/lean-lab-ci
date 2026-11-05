import LeanLab.HeathBrownPuchta.Decomp1530Core215

/-! P0012 page 30 display 44. Existing private certificate checks moved verbatim. -/
namespace LeanLab.HeathBrownPuchta.Decomp1530c
open Finset Real LeanLab.HeathBrownPuchta.Decomp1530a LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.Linnik
attribute [local instance 10] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open LeanLab.HeathBrownPuchta.Decomp1530c.CoreExports215

private lemma cbg32 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 32 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 32 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 32 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 32 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg33 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 33 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 33 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 33 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 33 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg34 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 34 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 34 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 34 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 34 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg35 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 35 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 35 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 35 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 35 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg36 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 36 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 36 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 36 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 36 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg37 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 37 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 37 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 37 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 37 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg38 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 38 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 38 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 38 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 38 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg39 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 39 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 39 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 39 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 39 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg40 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 40 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 40 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 40 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 40 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg41 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 41 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 41 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 41 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 41 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg42 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 42 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 42 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 42 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 42 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg43 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 43 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 43 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 43 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 43 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg44 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 44 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 44 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 44 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 44 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg45 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 45 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 45 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 45 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 45 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg46 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 46 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 46 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 46 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 46 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg47 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 47 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 47 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 47 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 47 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg48 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 48 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 48 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 48 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 48 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg49 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 49 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 49 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 49 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 49 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg50 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 50 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 50 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 50 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 50 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg51 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 51 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 51 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 51 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 51 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg52 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 52 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 52 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 52 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 52 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg53 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 53 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 53 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 53 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 53 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg54 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 54 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 54 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 54 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 54 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg55 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 55 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 55 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 55 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 55 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg56 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 56 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 56 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 56 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 56 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg57 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 57 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 57 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 57 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 57 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg58 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 58 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 58 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 58 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 58 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg59 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 59 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 59 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 59 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 59 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg60 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 60 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 60 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 60 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 60 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg61 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 61 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 61 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 61 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 61 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg62 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 62 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 62 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 62 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 62 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg63 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 63 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 63 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 63 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 63 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j


namespace GrhB215Exports
export LeanLab.HeathBrownPuchta.Decomp1530c (cbg32 cbg33 cbg34 cbg35 cbg36 cbg37 cbg38 cbg39 cbg40 cbg41 cbg42 cbg43 cbg44 cbg45 cbg46 cbg47 cbg48 cbg49 cbg50 cbg51 cbg52 cbg53 cbg54 cbg55 cbg56 cbg57 cbg58 cbg59 cbg60 cbg61 cbg62 cbg63)
end GrhB215Exports

end LeanLab.HeathBrownPuchta.Decomp1530c
