import LeanLab.ExceptionalSet.SPLIT_leaf_inner_low_j1

/-!
Split of `Decomp553c.leaf_low_j1_large_phase_localizes`, the localization step for
large values of the assigned lower block phase on the truncated minor window.

The target asks: for `γ` in `(1, 3 / 2)` there is a width `δ₀` and, for each
smaller positive `δ` and each `κ` below a cap `κ₀`, an eventual threshold `N₀`
such that on the truncated minor window every pair of points whose assigned lower
block phase exceeds `N E ^ (-(5 / 6))` differs by a point within `X ^ (δ - 1)` of
a half integer, where `X` is the exponential scale and `E` the cost parameter.

The step is cut into the two inputs its argument needs.

  * `leaf_low_j1_off_lattice_block_small` is the smallness of the block phase away
    from the half integer lattice: off the strips of radius `X ^ (δ - 1)` around the
    half integers of the bounded range, the restricted block sum is at most
    `N E ^ (-(5 / 6))`. It is one pointwise inequality about one block sum, with no
    existential conclusion, no width, no cap and no threshold in it, so it is
    strictly weaker than the target.
  * `leaf_low_j1_strip_index_bounded` is the arithmetic of the finite range: two
    points of the truncated window differ by at most `2 E ^ (2 / 3)`, the strip
    radius is at most one, and `4 E ^ (2 / 3) + 2 ≤ E ^ (3 / 4)` eventually, so an
    integer `h` with `|(b - a) - h / 2| ≤ X ^ (δ - 1)` satisfies
    `|h| ≤ E ^ (3 / 4)`. It carries neither a block phase nor a sum.

The assembly is pure logic: the width is one, the cap is one and the threshold is
zero, so every positive `δ` it is handed satisfies `δ ≤ 1`. If no half integer lies
within the strip radius of `b - a`, then every half integer of the bounded range is
off the strips, the first step bounds the block phase by `N E ^ (-(5 / 6))`, and
this contradicts the largeness hypothesis.

No existing file is edited, and the assembly does not use the target theorem.
-/

namespace LeanLab.ExceptionalSet.Decomp553c

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- LEAF. Step 1, the block phase is small off the half integer strips. At every
pair of points `a`, `b` of the truncated minor window, for every positive width
`δ` with `δ ≤ 1` and every positive `κ`, if `b - a` is further than `X ^ (δ - 1)`
from `h / 2` for every integer `h` with `|h| ≤ E ^ (3 / 4)`, then the assigned
lower block phase at `b - a` is at most `N E ^ (-(5 / 6))`. This is one pointwise
inequality about one block sum: it has no existential conclusion, no distance to a
half integer in its conclusion, and no threshold in any of its parameters, so it
is strictly weaker than the localization. -/
theorem leaf_low_j1_off_lattice_block_small (γ δ κ : ℝ) (N : ℕ) (a b : ℝ)
    (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ)
    (ha : a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N))
    (hb : b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N))
    (hoff : ∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
      F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) :
    ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ ≤
      (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  sorry

/-- LEAF. Step 2, the strip index is bounded. Two points of the truncated minor
window differ by at most `2 E ^ (2 / 3)`, the radius `X ^ (δ - 1)` is at most one
when `δ ≤ 1`, and `4 E ^ (2 / 3) + 2 ≤ E ^ (3 / 4)`; hence an integer `h` with
`|(b - a) - h / 2| ≤ X ^ (δ - 1)` satisfies `|h| ≤ E ^ (3 / 4)`. This is one
inequality between real numbers, with no block phase and no sum in it: it is the
range input that passes the distance condition to the finite strip union. -/
theorem leaf_low_j1_strip_index_bounded (γ δ κ : ℝ) (N : ℕ) (a b : ℝ) (h : ℤ)
    (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ)
    (ha : a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N))
    (hb : b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N))
    (hheight : 4 * calE γ κ N ^ (2 / 3 : ℝ) + 2 ≤ calE γ κ N ^ (3 / 4 : ℝ))
    (hh : |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1)) :
    (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) := by
  sorry

/-- Assembly. The two steps above localize the large values of the assigned lower
block phase. The width is fixed at one so every positive `δ` below it satisfies
`δ ≤ 1`, the cap on `κ` is one, the threshold is zero, and the rest is pure logic:
if no half integer is within the strip radius of `b - a`, the first step bounds the
block phase by `N E ^ (-(5 / 6))` and contradicts the largeness hypothesis. -/
theorem leaf_low_j1_large_phase_localizes_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                  ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ →
                ∃ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) := by
  refine ⟨1, one_pos, fun δ hδ hδone => ?_⟩
  have hδ1 : δ ≤ 1 := le_of_lt hδone
  refine ⟨1, one_pos, fun κ hκ _ => ?_⟩
  refine ⟨0, fun N _ a ha b hb hphase => ?_⟩
  by_contra hcon
  push Not at hcon
  exact absurd
    (leaf_low_j1_off_lattice_block_small γ δ κ N a b h1 h2 hδ hδ1 hκ ha hb
      (fun h _ => hcon h))
    (not_le.mpr hphase)

end LeanLab.ExceptionalSet.Decomp553c
