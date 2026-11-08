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

/-! ### Private helpers for the reduction below -/

/-- The family `l ↦ ⨆ (_ : l ∈ A), f l` is bounded above by the sum of the absolute values of `f`
over `A`: off `A` the supremum is taken over an empty index type, which is `0` in `ℝ`. -/
private lemma bddAbove_ciSup_finset (A : Finset ℕ) (f : ℕ → ℝ) :
    BddAbove (Set.range fun l => ⨆ (_ : l ∈ A), f l) := by
  refine ⟨∑ a ∈ A, |f a|, ?_⟩
  rintro _ ⟨l, rfl⟩
  dsimp only
  by_cases hl : l ∈ A
  · rw [ciSup_pos hl]
    exact le_trans (le_abs_self (f l))
      (Finset.single_le_sum (f := fun a => |f a|) (fun a _ => abs_nonneg (f a)) hl)
  · rw [ciSup_neg hl, Real.sSup_empty]
    exact Finset.sum_nonneg fun a _ => abs_nonneg (f a)

/-- A value of a finset-indexed supremum is at most the supremum. -/
private lemma le_ciSup_finset {A : Finset ℕ} {f : ℕ → ℝ} {l : ℕ} (hl : l ∈ A) :
    f l ≤ ⨆ l' ∈ A, f l' := by
  have h := le_ciSup (bddAbove_ciSup_finset A f) l
  rw [ciSup_pos hl] at h
  exact h

/-- The two-variable form of `le_ciSup_finset`. -/
private lemma le_ciSup_finset₂ {A B : Finset ℕ} {f : ℕ → ℕ → ℝ} {l₁ l₂ : ℕ}
    (h₁ : l₁ ∈ A) (h₂ : l₂ ∈ B) :
    f l₁ l₂ ≤ ⨆ l₁' ∈ A, ⨆ l₂' ∈ B, f l₁' l₂' := by
  have h2 : f l₁ l₂ ≤ ⨆ l₂' ∈ B, f l₁ l₂' := le_ciSup_finset h₂
  have h1 : (⨆ l₂' ∈ B, f l₁ l₂') ≤ ⨆ l₁' ∈ A, ⨆ l₂' ∈ B, f l₁' l₂' :=
    le_ciSup_finset (f := fun l₁' => ⨆ l₂' ∈ B, f l₁' l₂') h₁
  exact le_trans h2 h1

/-- A nonnegative family has a nonnegative supremum, including off `A`, where the index type of
the inner supremum is empty. -/
private lemma nonneg_ciSup_finset (A : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∀ l, 0 ≤ ⨆ (_ : l ∈ A), f l := by
  intro l
  by_cases hl : l ∈ A
  · rw [ciSup_pos hl]
    exact hf l
  · rw [ciSup_neg hl, Real.sSup_empty]

/-- The two-variable nonnegativity of a supremum over residues. -/
private lemma nonneg_ciSup_finset₂ {A B : Finset ℕ} (f : ℕ → ℕ → ℝ) (hf : ∀ a b, 0 ≤ f a b) :
    0 ≤ ⨆ l₁ ∈ A, ⨆ l₂ ∈ B, f l₁ l₂ := by
  have key : ∀ l₁, 0 ≤ ⨆ (_ : l₁ ∈ A), ⨆ l₂ ∈ B, f l₁ l₂ :=
    nonneg_ciSup_finset A (fun a => ⨆ l₂ ∈ B, f a l₂)
      (fun a => Real.iSup_nonneg (f := fun l₂ => ⨆ (_ : l₂ ∈ B), f a l₂)
        (fun l₂ => nonneg_ciSup_finset B (fun b => f a b) (hf a) l₂))
  exact Real.iSup_nonneg (f := fun l₁ => ⨆ (_ : l₁ ∈ A), ⨆ l₂ ∈ B, f l₁ l₂) key

/-- A bound holding for every pair bounds the two-variable supremum. The hypothesis `0 ≤ X` is
needed for the `l` outside `A` or `B`, where the supremum is over an empty index type. -/
private lemma ciSup_finset₂_le {A B : Finset ℕ} {f : ℕ → ℕ → ℝ} {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ l₁ ∈ A, ∀ l₂ ∈ B, f l₁ l₂ ≤ X) :
    (⨆ l₁ ∈ A, ⨆ l₂ ∈ B, f l₁ l₂) ≤ X := by
  have key : ∀ l₁, (⨆ (_ : l₁ ∈ A), ⨆ l₂ ∈ B, f l₁ l₂) ≤ X := by
    intro l₁
    by_cases h₁ : l₁ ∈ A
    · rw [ciSup_pos h₁]
      have key2 : ∀ l₂, (⨆ (_ : l₂ ∈ B), f l₁ l₂) ≤ X := by
        intro l₂
        by_cases h₂ : l₂ ∈ B
        · rw [ciSup_pos h₂]
          exact h l₁ h₁ l₂ h₂
        · rw [ciSup_neg h₂, Real.sSup_empty]
          exact hX
      exact ciSup_le (f := fun l₂ => ⨆ (_ : l₂ ∈ B), f l₁ l₂) key2
    · rw [ciSup_neg h₁, Real.sSup_empty]
      exact hX
  exact ciSup_le (f := fun l₁ => ⨆ (_ : l₁ ∈ A), ⨆ l₂ ∈ B, f l₁ l₂) key

/-- The triangle inequality in the form the reduction uses it. -/
private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le a, le_abs_self b]
  · linarith [le_abs_self a, neg_le_abs b]

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
  simp only [Estar, inner]
  calc
    ∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊, ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊, ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
              |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * Δ S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|
        ≤ ∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊, ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊, ((⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
              |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * R ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|) + (⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
              |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * M S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|)) := by
      refine Finset.sum_le_sum fun k₁ _ => Finset.sum_le_sum fun k₂ _ => ?_
      refine ciSup_finset₂_le ?_ fun l₁ hl₁ l₂ hl₂ => ?_
      · refine add_nonneg ?_ ?_
        · exact nonneg_ciSup_finset₂ (f := fun a b => |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * R ![k₁, k₂, k₃] ![a, b, l₃] N|)
            (fun a b => abs_nonneg _)
        · exact nonneg_ciSup_finset₂ (f := fun a b => |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * M S ![k₁, k₂, k₃] ![a, b, l₃] N|)
            (fun a b => abs_nonneg _)
      · have hΔ :
            (∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃),
              lam k₃ * Δ S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N)
              = (∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃),
                lam k₃ * R ![k₁, k₂, k₃] ![l₁, l₂, l₃] N) -
                (∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃),
                  lam k₃ * M S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N) := by
          simp only [Δ, mul_sub, Finset.sum_sub_distrib]
        rw [hΔ]
        refine le_trans (abs_sub_le_abs_add _ _) ?_
        refine add_le_add ?_ ?_
        · exact le_ciSup_finset₂ (f := fun a b => |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * R ![k₁, k₂, k₃] ![a, b, l₃] N|) hl₁ hl₂
        · exact le_ciSup_finset₂ (f := fun a b => |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * M S ![k₁, k₂, k₃] ![a, b, l₃] N|) hl₁ hl₂
    _ = (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊, ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊, ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
              |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * R ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|) +
        (∑ k₁ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊, ∑ k₂ ∈ Icc 1 ⌊Real.sqrt N * Real.log N ^ (-B)⌋₊, ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
              |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * M S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|) := by
      simp only [Finset.sum_add_distrib]


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
