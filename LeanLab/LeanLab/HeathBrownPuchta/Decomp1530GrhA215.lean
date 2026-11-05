import LeanLab.HeathBrownPuchta.Decomp1530Core215

/-! P0012 page 30 display 44. Existing private certificate checks moved verbatim. -/
namespace LeanLab.HeathBrownPuchta.Decomp1530c
open Finset Real LeanLab.HeathBrownPuchta.Decomp1530a LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.Linnik
attribute [local instance 10] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open LeanLab.HeathBrownPuchta.Decomp1530c.CoreExports215

private lemma cbg0 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 0 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 0 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 0 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 0 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg1 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 1 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 1 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 1 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 1 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg2 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 2 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 2 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 2 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 2 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg3 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 3 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 3 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 3 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 3 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg4 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 4 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 4 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 4 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 4 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg5 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 5 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 5 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 5 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 5 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg6 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 6 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 6 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 6 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 6 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg7 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 7 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 7 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 7 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 7 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg8 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 8 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 8 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 8 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 8 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg9 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 9 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 9 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 9 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 9 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg10 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 10 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 10 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 10 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 10 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg11 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 11 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 11 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 11 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 11 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg12 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 12 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 12 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 12 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 12 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg13 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 13 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 13 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 13 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 13 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg14 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 14 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 14 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 14 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 14 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg15 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 15 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 15 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 15 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 15 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg16 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 16 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 16 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 16 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 16 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg17 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 17 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 17 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 17 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 17 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg18 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 18 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 18 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 18 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 18 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg19 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 19 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 19 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 19 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 19 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg20 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 20 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 20 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 20 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 20 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg21 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 21 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 21 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 21 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 21 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg22 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 22 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 22 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 22 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 22 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg23 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 23 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 23 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 23 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 23 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg24 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 24 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 24 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 24 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 24 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg25 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 25 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 25 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 25 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 25 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg26 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 26 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 26 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 26 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 26 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg27 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 27 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 27 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 27 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 27 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg28 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 28 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 28 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 28 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 28 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg29 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 29 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 29 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 29 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 29 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg30 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 30 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 30 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 30 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 30 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbg31 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * 31 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 31 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (905 * cc (128 * (4 * 31 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * 31 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j


namespace GrhA215Exports
export LeanLab.HeathBrownPuchta.Decomp1530c (cbg0 cbg1 cbg2 cbg3 cbg4 cbg5 cbg6 cbg7 cbg8 cbg9 cbg10 cbg11 cbg12 cbg13 cbg14 cbg15 cbg16 cbg17 cbg18 cbg19 cbg20 cbg21 cbg22 cbg23 cbg24 cbg25 cbg26 cbg27 cbg28 cbg29 cbg30 cbg31)
end GrhA215Exports

end LeanLab.HeathBrownPuchta.Decomp1530c
