import LeanLab.ExceptionalSet.SPLIT_leaf_moment_nu_succ

/-!
Split of `leaf_moment_nu_succ_even` of `LeanLab.ExceptionalSet.SPLIT_leaf_moment_nu_succ`, the
centered second moment of `(R1 (X^(6δ)) X (nu γ n + 1)).re` about the main term `X/2`, with
`X = F γ N`, over the even indices of the window `X/2 < F γ n ≤ X`, `n ≤ 2N`.

Source: P0082, Brüdern and Perelli 1998, page 367, displays 28 to 30 and the deduction of
Lemma 6 there.  The paper bounds moments about zero on parity classes; the source audit in the
original file records that the centered form also needs a first moment.  By
`MomentNuSuccSplit.centered_moment_expansion`,
`∑ (X/2 - g)^2 = (∑ g^2 - |s| (X/2)^2) + X (|s| X/2 - ∑ g)`, so the leaves are
* the second moment about zero of `g` on the block compared with the square of the main term,
  the analogue of displays 29 and 30, and
* the first moment of `g` on the block, which must reproduce the main term `X/2` per index
  up to the same saving, from the major arc evaluation behind display 28.
The assembly is algebra plus the bookkeeping of the caps `δ₀`, `κ₀`.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.U1539

namespace MomentNuSuccSplit

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: P0082 page 367 displays 29 and 30, second moment about zero on a parity block: over the
even `n ≤ 2N` with `F γ N / 2 < F γ n ≤ F γ N`, the sum of the squares of
`(R1 (X^(6δ)) X (nu γ n + 1)).re` exceeds `|block| (X/2)^2` by at most
`B N X^2 calE^(-17/60)`.  Class HARD. -/
theorem leaf_moment_nu_succ_even_second (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => Even n),
            ((R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2) -
            (((((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => Even n)).card : ℝ) * (F γ N / 2) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  sorry

/-- LEAF: P0082 page 367 display 28 with the major arc evaluation used for Lemma 6, first moment on
a parity block: over the even `n ≤ 2N` with `F γ N / 2 < F γ n ≤ F γ N`, the sum of
`(R1 (X^(6δ)) X (nu γ n + 1)).re` falls short of `|block| X/2` by an amount whose product with
`X` is at most `B N X^2 calE^(-17/60)`.  Class HARD. -/
theorem leaf_moment_nu_succ_even_first (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          F γ N * ((((((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => Even n)).card : ℝ) * (F γ N / 2)) -
            ∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => Even n),
              (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  sorry

/-- Assembly of the original parity leaf from the second moment and first moment leaves. -/
theorem leaf_moment_nu_succ_even_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => Even n),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  classical
  obtain ⟨δ₁, hδ₁, hA⟩ := leaf_moment_nu_succ_even_second γ h1 h2
  obtain ⟨δ₂, hδ₂, hB⟩ := leaf_moment_nu_succ_even_first γ h1 h2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₁, hκ₁, hA⟩ := hA δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κ₂, hκ₂, hB⟩ := hB δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B₁, hB₁, N₁, hA⟩ := hA κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨B₂, hB₂, N₂, hB⟩ := hB κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨B₁ + B₂, add_pos hB₁ hB₂, max N₁ N₂, fun N hN => ?_⟩
  have a := hA N ((le_max_left _ _).trans hN)
  have b := hB N ((le_max_right _ _).trans hN)
  rw [centered_moment_expansion]
  have e : (B₁ + B₂) * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) =
      B₁ * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) +
        B₂ * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by ring
  rw [e]
  nlinarith [a, b]

end MomentNuSuccSplit

end LeanLab.ExceptionalSet.U1539
