/-
Split of `LeanLab.ExceptionalSet.U1539.leaf_moment_nu` into the two halves of its
index window.

The target is a second moment of the real part of the adjacent major arc
coefficient over the window `X/2 < F(n) <= X` of the indices `n <= 2N`, where
`X = F(N)`.  The cut here is inside the index range, at `n <= N`: one leaf is the
same second moment over the lower half of the range, one leaf over the upper half,
and the assembly adds them.

Each leaf is a sub-sum of the target's sum, and the summand is a square, hence
nonnegative, so the target implies either leaf while neither leaf alone implies
the target: each is strictly weaker than it.  The two leaves together, with the
constant `B1 + B2`, the lower of the two `delta` caps and the lower of the two
`kappa` caps, give the target.  No cardinality is bounded anywhere in this file,
and neither leaf restates or assumes the target.

The whole analytic content sits in the two leaves.  For `1 < gamma < 3/2` the
squared deviation of the real part of `R1` at `nu_n` from the main term `X/2`,
summed over a sub-range of the window of `n <= 2N`, is eventually at most
`B N X^2 E^(-17/60)` with `E = calE(N)`: one half of the section 6 second moment
of the odd adjacent coefficient, cut at the middle of the index range.

LEAN CODE WRITTEN BY AI, CHECKED ONLY BY THE KERNEL.  BINARY GOLDBACH IS OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma7

namespace LeanLab.ExceptionalSet.U1539

namespace MomentNuSplit

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF: the lower half of the index range of the second moment of Lemma 7, that
is the same estimate as the target restricted to the indices `n <= N` of the
window `F γ N / 2 < F γ n <= F γ N`, with `n <= 2N + 1`.  This is a sub-range of
the target's index set and the summand is a square, so the target implies this
statement and this statement alone does not imply the target: it is strictly
weaker.  No cardinality is bounded.

Non-vacuity: `γ = 5/4` is allowed; at `N = 0` the range is `{0}`, the lower block
is `{0}` and reads one square against a right side that is `0`, which is why the
threshold `N₀` is part of the statement; if the window is empty the left side is
`0` against the positive right side `B * N * F γ N ^ 2 * calE γ κ N ^ (-17/60)`
for `B > 0` and `N ≥ 1`.  Division is only by the numeral `2`, and the base of the
real power `F γ N ^ (6 * δ)` is positive, so no junk value enters. -/
theorem leaf_moment_nu_low (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => n ≤ N),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  sorry

/-- LEAF: the upper half of the index range of the same second moment of Lemma 7,
that is the same estimate restricted to the indices `N < n` of the window
`F γ N / 2 < F γ n <= F γ N`, with `n <= 2N + 1`.  Again a sub-range of the
target's index set with a square summand, hence strictly weaker than the target,
and, like the lower leaf, no cardinality is bounded.

Non-vacuity: at `N = 0` and `N = 1` this block is empty and the estimate reads
`0` against the right side, which is nonnegative for `B > 0`; at `γ = 5/4` and
large `N` the block is the upper half of the window.  The two leaves together
partition the target's index set, `n <= N` or `N < n`, so no index is counted
twice and none is lost.  Division is only by the numeral `2`, and the base of the
real power `F γ N ^ (6 * δ)` is positive, so no junk value enters. -/
theorem leaf_moment_nu_high (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
              (fun n : ℕ => ¬ n ≤ N),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  sorry

/-! ### Assembly -/

/-- The assembly of the target from its two halves: the two leaves are minimised
in their caps, the constant is their sum, and the two sub-sums are put back
together by the finite identity `∑_{n ≤ N} + ∑_{N < n} = ∑` over the window.  No
analysis enters here. -/
theorem leaf_moment_nu_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  classical
  obtain ⟨δ₁, hδ₁, hlow⟩ := leaf_moment_nu_low γ h1 h2
  obtain ⟨δ₂, hδ₂, hhigh⟩ := leaf_moment_nu_high γ h1 h2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₁, hκ₁, hlow⟩ := hlow δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κ₂, hκ₂, hhigh⟩ := hhigh δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B₁, hB₁, N₁, hlow⟩ := hlow κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨B₂, hB₂, N₂, hhigh⟩ := hhigh κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨B₁ + B₂, add_pos hB₁ hB₂, max N₁ N₂, fun N hN => ?_⟩
  have h₁ := hlow N ((le_max_left _ _).trans hN)
  have h₂ := hhigh N ((le_max_right _ _).trans hN)
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.range (2 * N + 1)).filter
      (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)) (fun n : ℕ => n ≤ N)]
  refine (add_le_add h₁ h₂).trans_eq ?_
  ring

end MomentNuSplit

end LeanLab.ExceptionalSet.U1539
