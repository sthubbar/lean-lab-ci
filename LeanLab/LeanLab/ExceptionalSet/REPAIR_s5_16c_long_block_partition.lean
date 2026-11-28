import LeanLab.ExceptionalSet.SPLIT_leaf_small_case

/-!
A repair step for the split `SPLIT_leaf_small_case`, by CLOUD S5 burst-20261127, KEEP GOING
from unit S5-16.

The LEAF `leaf_small_block_sum_bound` of that split is false as stated, see
`FALSE_s5_16b_small_block_sum_bound.lean`: it asks for the saving on blocks of every length
`m ≤ [P^(c1 - c4/2)]`, while the saving of p. 248 of Karacuba, chapter I section 2, comes
from the denominator bound `q ≤ P^(c2 s) < m^s`, which needs `m` near `P^(c1 - c4/2)`.
The partition of p. 248 uses blocks of the full length `L` only, plus one leftover block that
is bounded trivially. This file proves that partition bound: full blocks of length `L` with
the bound `C L^(1-ρ)`, and terms of norm at most one, give
`|Σ_{[N, N+P₁)} g| ≤ (P₁/L) C L^(1-ρ) + L`. The extra `L = [P^δ]` is below `P^(1-γ/n²)`
whenever `γ/n² ≤ 1 - δ`, which the bookkeeping of the split already arranges.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit.RepairS5

/-- The p. 248 partition with full blocks only: if every full block `[a, a+L)` inside
`[S, E]` has sum at most `W` in norm, and every term has norm at most one, then every sum
over `[N, N+P₁)` inside `[S, E]` is at most `(P₁/L) W + L`. -/
theorem block_partition_bound_full (g : ℕ → ℂ) (W : ℝ) (L : ℕ) (hL : 0 < L) (hW : 0 ≤ W)
    (S E : ℕ) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hblk : ∀ a : ℕ, S ≤ a → a + L ≤ E → ‖∑ x ∈ Finset.Ico a (a + L), g x‖ ≤ W) :
    ∀ (P₁ N : ℕ), S ≤ N → N + P₁ ≤ E →
      ‖∑ x ∈ Finset.Ico N (N + P₁), g x‖ ≤ (P₁ : ℝ) / (L : ℝ) * W + L := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  intro P₁
  induction P₁ using Nat.strong_induction_on with
  | _ P₁ ih =>
    intro N hSN hNE
    rcases Nat.lt_or_ge P₁ L with hPL | hLP
    · have htriv : ‖∑ x ∈ Finset.Ico N (N + P₁), g x‖ ≤ (P₁ : ℝ) := by
        calc ‖∑ x ∈ Finset.Ico N (N + P₁), g x‖
            ≤ ∑ x ∈ Finset.Ico N (N + P₁), ‖g x‖ := norm_sum_le _ _
          _ ≤ ∑ x ∈ Finset.Ico N (N + P₁), (1 : ℝ) := Finset.sum_le_sum (fun x _ => hg x)
          _ = (P₁ : ℝ) := by simp
      have hPLr : (P₁ : ℝ) ≤ L := by exact_mod_cast hPL.le
      have h0 : 0 ≤ (P₁ : ℝ) / (L : ℝ) * W := by positivity
      linarith
    · have hsplit : ∑ x ∈ Finset.Ico N (N + P₁), g x
          = ∑ x ∈ Finset.Ico N (N + L), g x + ∑ x ∈ Finset.Ico (N + L) (N + P₁), g x :=
        (Finset.sum_Ico_consecutive g (m := N) (n := N + L) (k := N + P₁)
          (by omega) (by omega)).symm
      rw [hsplit]
      have hfirst := hblk N hSN (by omega)
      have htail : ‖∑ x ∈ Finset.Ico (N + L) (N + P₁), g x‖ ≤
          ((P₁ - L : ℕ) : ℝ) / (L : ℝ) * W + L := by
        have hidx : (N + L) + (P₁ - L) = N + P₁ := by omega
        have h := ih (P₁ - L) (by omega) (N + L) (by omega) (by omega)
        rw [hidx] at h
        exact h
      have hcast : ((P₁ - L : ℕ) : ℝ) = (P₁ : ℝ) - (L : ℝ) := by
        push_cast [Nat.cast_sub hLP]
        ring
      rw [hcast] at htail
      have hid : ((P₁ : ℝ) - L) / L * W + W = (P₁ : ℝ) / L * W := by
        field_simp
        ring
      calc ‖∑ x ∈ Finset.Ico N (N + L), g x + ∑ x ∈ Finset.Ico (N + L) (N + P₁), g x‖
          ≤ ‖∑ x ∈ Finset.Ico N (N + L), g x‖ + ‖∑ x ∈ Finset.Ico (N + L) (N + P₁), g x‖ :=
            norm_add_le _ _
        _ ≤ W + (((P₁ : ℝ) - L) / L * W + L) := add_le_add hfirst htail
        _ = (P₁ : ℝ) / (L : ℝ) * W + L := by linarith

end LeanLab.ExceptionalSet.U1539.KaracubaSplit.RepairS5
