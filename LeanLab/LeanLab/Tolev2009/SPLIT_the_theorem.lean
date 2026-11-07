/-
Split of `the_theorem` of `LeanLab/Tolev2009/Representations.lean` into smaller leaves.

The sealed statement is `TheTheorem halupczokS`: for every `A > 0` there is `B > 0` such that
the averaged error `E*` is at most `C * N^2 * (log N)^(-A)` for odd `N`, uniformly in the weight
`lam` with `|lam k| <= 1` and in the residue `l3 >= 1`.

The split separates the two halves of the error `Delta = R - M`, keeping the supremum over the
residues `l1, l2` and the double sum over the moduli `k1, k2` on each half:

* `leaf_error_part_average` is the average of the weighted prime-counting error `R`;
* `leaf_main_part_average` is the same average of the explicit main term `M`;
* `leaf_estar_le_parts` is the reduction that passes from `Delta` to the two halves.

`the_theorem_split` assembles them. This file adds no definition and changes no statement.

AI-written Lean code. Checked only by the Lean kernel.
-/
import LeanLab.Tolev2009.Representations

open Finset Real

namespace LeanLab.Tolev2009.Reps

/-- LEAF The averaging step for the weighted prime count `R`, the hard half of the error: the
double sum over `k1, k2 <= floor (sqrt N * (log N)^(-B))` of the supremum over the admissible
residues `l1, l2` of the absolute weighted `k3`-sum of `R` is at most `C * N^2 * (log N)^(-A)`,
for some `B = B(A)`. It is one of the two halves the sealed statement adds up. -/
theorem leaf_error_part_average :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ,
      (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
        (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
            ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
              ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
                |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
                    (fun k₃ => Nat.Coprime k₃ l₃),
                  lam k₃ * R ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|)
          ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  sorry

/-- LEAF The averaging step for the explicit main term `M = N^2 S / (2 phi k1 phi k2 phi k3)`:
the same double sum and supremum, with `M` in place of `R`, is at most `C * N^2 * (log N)^(-A)`
for every `B > 0`, the constant `C` absorbing the size of the series `halupczokS` up to
`(log N)^A`. This half carries no prime-counting difficulty; it needs a size for `halupczokS`,
which is opaque here. -/
theorem leaf_main_part_average :
    ∀ A : ℝ, 0 < A → ∀ B : ℝ, 0 < B → ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ,
      (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
        (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
            ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
              ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
                |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
                    (fun k₃ => Nat.Coprime k₃ l₃),
                  lam k₃ * M halupczokS ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|)
          ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  sorry

/-- LEAF The reduction from `Delta = R - M` to its two halves: the averaged error `E*` is at
most the `R` average plus the `M` average. The step is the triangle inequality
`|R - M| <= |R| + |M|` carried through the finite `k3`-sum, the supremum over `l1, l2` and the
double sum over `k1, k2`. -/
theorem leaf_estar_le_parts (S : SSeries) (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    Estar S lam l₃ B N ≤
      (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
          ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
            ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
              |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
                  (fun k₃ => Nat.Coprime k₃ l₃),
                lam k₃ * R ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|) +
      (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
          ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊,
            ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
              |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
                  (fun k₃ => Nat.Coprime k₃ l₃),
                lam k₃ * M S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|) := by
  sorry

/-- The sealed statement, assembled from the three leaves. Its statement is the target's,
character for character. -/
theorem the_theorem_split : TheTheorem halupczokS := by
  intro A hA
  obtain ⟨B, hBpos, hB⟩ := leaf_error_part_average A hA
  refine ⟨B, hBpos, fun l₃ hl₃ => ?_⟩
  obtain ⟨C₁, N₁, h₁⟩ := hB l₃ hl₃
  obtain ⟨C₂, N₂, h₂⟩ := leaf_main_part_average A hA B hBpos l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, fun lam hlam N hodd hN => ?_⟩
  have hN₁ : N₁ ≤ N := le_trans (le_max_left N₁ N₂) hN
  have hN₂ : N₂ ≤ N := le_trans (le_max_right N₁ N₂) hN
  refine le_trans (leaf_estar_le_parts halupczokS lam l₃ B N)
    (le_trans (add_le_add (h₁ lam hlam N hodd hN₁) (h₂ lam hlam N hodd hN₂)) ?_)
  have hsum :
      C₁ * (N : ℝ) ^ 2 * Real.log N ^ (-A) + C₂ * (N : ℝ) ^ 2 * Real.log N ^ (-A)
        = (C₁ + C₂) * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by ring
  linarith [hsum]

end LeanLab.Tolev2009.Reps
