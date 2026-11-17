/-
Split of `LeanLab.ExceptionalSet.U1539.leaf_moment_nu_succ` into the two parity
classes of its index window.

The target is a second moment of the real part of the adjacent major arc coefficient at
the neighbour index `nu_n + 1`, over the window `X/2 < F(n) <= X` of the indices
`n <= 2N`, where `X = F(N)`. The cut here is inside the index set and follows the parity
of the index, which is the division the surrounding argument of this folder already uses
for its pair `nu_n, nu_n + 1`: one leaf is the same second moment restricted to the even
indices of the window, one to the odd indices, and the assembly adds the two.

Each leaf is a sub-sum of the target's sum over a subset of its index set, and the
summand is a square, hence nonnegative, so the target implies either leaf while neither
leaf alone implies the target: each is strictly weaker than it. The two leaves together,
with the constant `B1 + B2`, the lower of the two `delta` caps and the lower of the two
`kappa` caps, give the target. No cardinality is bounded anywhere in this file, no leaf
restates or assumes the target, and neither block is empty: the window is the band of
indices just below `n = N`, of length asymptotic to `N log 2 / (gamma * (log N)^(gamma-1))`,
which tends to infinity with `N`, so from some `N` on it holds indices of both parities.

The whole analytic content sits in the two leaves. For `1 < gamma < 3/2` the squared
deviation of the real part of `R1` at `nu_n + 1` from the main term `X/2`, summed over
the even (respectively odd) part of the window of `n <= 2N`, is eventually at most
`B N X^2 E^(-17/60)` with `E = calE(N)`.

LEAN CODE WRITTEN BY AI, CHECKED ONLY BY THE KERNEL.  BINARY GOLDBACH IS OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma7

namespace LeanLab.ExceptionalSet.U1539

namespace MomentNuSuccSplit

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-
Source audit, task1044: P0082 page 367 displays 29 and 30 bound moments about zero
on the parity classes of `nu γ n`, not centered moments on the parity classes of `n`.
The expansion below isolates the first-moment cancellation still needed here.
-/

/-- Algebraic expansion of the centered moment. The term linear in `g` is needed
in addition to an uncentered second moment. -/
theorem centered_moment_expansion (s : Finset ℕ) (g : ℕ → ℝ) (X : ℝ) :
    (∑ n ∈ s, (X / 2 - g n) ^ 2) =
      (s.card : ℝ) * (X / 2) ^ 2 - X * (∑ n ∈ s, g n) +
        ∑ n ∈ s, (g n) ^ 2 := by
  calc
    _ = ∑ n ∈ s, ((X / 2) ^ 2 - X * g n + (g n) ^ 2) := by
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum]

/-- LEAF: the even indices of the index window of the second moment at `nu γ n + 1`,
over `F γ N / 2 < F γ n <= F γ N`, `n <= 2N + 1`: the squared deviation of the real
part of `R1` from the main term `X/2`, summed over the even `n` of the window. A
sub-sum of the target's index set with a square summand, so strictly weaker than the
target, and no cardinality is bounded. Non-vacuity: the window is the band just below
`n = N`, of length asymptotic to `N log 2 / (γ (log N)^(γ-1))`, which tends to
infinity, so it holds even indices for all large `N`; at `N = 0` the even block is
`{0}` while the right side is `0`, so the threshold `N₀` belongs to the statement.
Division is only by the numeral `2` and the base of the real power is positive, so no
junk value enters. -/
theorem leaf_moment_nu_succ_even (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => Even n),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  classical
  simp_rw [centered_moment_expansion]
  sorry

/-- LEAF: the odd indices of the same index window of the same second moment at
`nu γ n + 1`, over `F γ N / 2 < F γ n <= F γ N`, `n <= 2N + 1`: the same squared
deviation of the real part of `R1` from `X/2`, summed over the `n` with `¬ Even n`.
Again a sub-sum with a square summand, hence strictly weaker than the target, and no
cardinality is bounded. Non-vacuity: the window holds odd indices for all large `N`;
at small `N` the block may be empty and reads `0` against a nonnegative right side.
With the even leaf it partitions the target's index set, `Even n` or `¬ Even n`, so
no index is counted twice and none is lost. Division is only by the numeral `2` and
the base of the real power is positive, so no junk value enters. -/
theorem leaf_moment_nu_succ_odd (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => ¬ Even n),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  classical
  simp_rw [centered_moment_expansion]
  sorry

/-! ### Assembly -/

/-- The assembly of the target from its two parity blocks: the two leaves are minimised
in their caps, the constant is their sum, and the two sub-sums are put back together by
the finite identity `∑_{even} + ∑_{odd} = ∑` over the window. No analysis enters here. -/
theorem leaf_moment_nu_succ_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  classical
  obtain ⟨δ₁, hδ₁, heven⟩ := leaf_moment_nu_succ_even γ h1 h2
  obtain ⟨δ₂, hδ₂, hodd⟩ := leaf_moment_nu_succ_odd γ h1 h2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₁, hκ₁, heven⟩ := heven δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κ₂, hκ₂, hodd⟩ := hodd δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B₁, hB₁, N₁, heven⟩ := heven κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨B₂, hB₂, N₂, hodd⟩ := hodd κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨B₁ + B₂, add_pos hB₁ hB₂, max N₁ N₂, fun N hN => ?_⟩
  have h₁ := heven N ((le_max_left _ _).trans hN)
  have h₂ := hodd N ((le_max_right _ _).trans hN)
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.range (2 * N + 1)).filter
      (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)) (fun n : ℕ => Even n)]
  refine (add_le_add h₁ h₂).trans_eq ?_
  ring

end MomentNuSuccSplit

end LeanLab.ExceptionalSet.U1539
