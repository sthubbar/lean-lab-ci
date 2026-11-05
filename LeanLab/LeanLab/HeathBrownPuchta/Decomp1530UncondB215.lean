import LeanLab.HeathBrownPuchta.Decomp1530Core215

/-! P0012 page 30 display 44. Existing private certificate checks moved verbatim. -/
namespace LeanLab.HeathBrownPuchta.Decomp1530c
open Finset Real LeanLab.HeathBrownPuchta.Decomp1530a LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.Linnik
attribute [local instance 10] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open LeanLab.HeathBrownPuchta.Decomp1530c.CoreExports215

private lemma cbu32 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 32 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 32 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 32 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 32 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu33 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 33 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 33 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 33 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 33 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu34 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 34 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 34 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 34 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 34 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu35 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 35 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 35 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 35 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 35 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu36 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 36 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 36 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 36 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 36 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu37 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 37 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 37 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 37 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 37 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu38 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 38 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 38 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 38 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 38 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu39 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 39 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 39 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 39 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 39 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu40 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 40 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 40 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 40 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 40 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu41 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 41 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 41 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 41 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 41 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu42 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 42 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 42 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 42 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 42 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu43 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 43 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 43 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 43 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 43 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu44 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 44 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 44 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 44 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 44 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu45 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 45 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 45 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 45 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 45 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu46 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 46 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 46 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 46 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 46 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu47 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 47 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 47 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 47 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 47 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu48 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 48 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 48 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 48 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 48 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu49 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 49 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 49 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 49 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 49 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu50 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 50 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 50 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 50 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 50 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu51 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 51 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 51 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 51 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 51 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu52 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 52 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 52 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 52 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 52 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu53 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 53 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 53 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 53 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 53 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu54 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 54 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 54 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 54 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 54 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu55 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 55 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 55 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 55 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 55 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu56 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 56 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 56 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 56 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 56 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu57 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 57 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 57 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 57 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 57 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu58 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 58 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 58 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 58 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 58 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu59 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 59 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 59 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 59 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 59 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu60 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 60 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 60 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 60 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 60 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu61 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 61 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 61 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 61 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 61 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu62 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 62 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 62 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 62 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 62 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j

private lemma cbu63 : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * 63 + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 63 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have h : ∀ j : Fin 4,
    (1000 : ℤ) * (∑ b ∈ range 16, ∑ r ∈ range 8, mexp (1181 * cc (128 * (4 * 63 + j.val) + (8 * b + r) + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * 63 + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by decide +kernel
  intro j
  rw [sum128_split215]
  exact h j


namespace UncondB215Exports
export LeanLab.HeathBrownPuchta.Decomp1530c (cbu32 cbu33 cbu34 cbu35 cbu36 cbu37 cbu38 cbu39 cbu40 cbu41 cbu42 cbu43 cbu44 cbu45 cbu46 cbu47 cbu48 cbu49 cbu50 cbu51 cbu52 cbu53 cbu54 cbu55 cbu56 cbu57 cbu58 cbu59 cbu60 cbu61 cbu62 cbu63)
end UncondB215Exports

end LeanLab.HeathBrownPuchta.Decomp1530c
