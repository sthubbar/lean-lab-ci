import LeanLab.ExceptionalSet.SPLIT_leaf_inner_high_j1

/-!
Split of `Decomp553d.leaf_high_j1_large_phase_localizes`, the localization step
for large values of the assigned upper block phase on the truncated minor window.

The target asks: for parameters `γ` in `(1, 3 / 2)` there is a width `δ₀` and,
for each smaller positive `δ` and each `κ` below a cap `κ₀`, an eventual
threshold `N₀` such that on the truncated minor window every pair of points whose
assigned upper block phase exceeds `N E ^ (-(5 / 6))` differs by a point within
`X ^ (δ - 1)` of a half integer.

The step is cut into the two inputs its argument needs.

  * `leaf_high_j1_off_lattice_block_small` is the smallness of the block phase
    away from the half integer lattice: off the strips of radius `X ^ (δ - 1)`
    around the half integers the restricted block sum is at most
    `N E ^ (-(5 / 6))`. It is one inequality about one sum, it has no
    existential conclusion and no distance to a half integer, so it is strictly
    weaker than the target: it is the contrapositive of the target restricted to
    the finitely many half integers that can occur.
  * `leaf_high_j1_strip_index_bounded` is the arithmetic of that finite range:
    two points of the truncated window are at distance at most `2 E ^ (2 / 3)`
    and the strip radius is at most one, so a half integer within
    `X ^ (δ - 1)` of their difference is bounded by `E ^ (3 / 4)`. This carries
    no phase and no sum.

The assembly is pure logic: if no half integer is within the strip radius of
`b - a`, then every half integer of the bounded range is off the strips, the
first step bounds the block phase by `N E ^ (-(5 / 6))`, and this contradicts
the largeness hypothesis.

No existing file is edited. The assembly does not use the target theorem.
-/

namespace LeanLab.ExceptionalSet.Decomp553d

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- LEAF. Step 1, the block phase is small off the half integer strips. For every
admissible width `δ` and every admissible cap for `κ` there is an eventual
threshold such that, at every point `a` and every point `b` of the truncated
minor window, if `b - a` is further than `X ^ (δ - 1)` from `h / 2` for every
integer `h` with `|h| ≤ E ^ (3 / 4)`, then the assigned upper block phase at
`b - a` is at most `N E ^ (-(5 / 6))`. This is one inequality about one block
sum, with no existential conclusion: it is the localization content of the
target read in contrapositive form on a bounded range of half integers, hence
strictly weaker. -/
theorem leaf_high_j1_off_lattice_block_small (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖blockPhase (indices_high_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  sorry

/-- LEAF. Step 2, the strip index is bounded. Two points of the truncated minor
window differ by at most `2 E ^ (2 / 3)`, the strip radius is at most one, and
`4 E ^ (2 / 3) + 2 ≤ E ^ (3 / 4)` eventually; hence any integer `h` with
`|(b - a) - h / 2| ≤ X ^ (δ - 1)` satisfies `|h| ≤ E ^ (3 / 4)`. This is one
inequality between real numbers: it involves neither the block phase nor any
sum, so it is strictly weaker than the target. -/
theorem leaf_high_j1_strip_index_bounded (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              ∀ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) →
                (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) := by
  sorry

/-- Assembly. The two steps above localize the large values of the assigned
upper block phase. If no half integer is within the strip radius of `b - a`, the
second step puts every candidate index inside the bounded range, the first step
then bounds the block phase by `N E ^ (-(5 / 6))`, and the largeness hypothesis
is contradicted. -/
theorem leaf_high_j1_large_phase_localizes_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                  ‖blockPhase (indices_high_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ →
                ∃ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) := by
  obtain ⟨δa, hδa, hoff⟩ := leaf_high_j1_off_lattice_block_small γ h1 h2
  obtain ⟨δb, hδb, hidx⟩ := leaf_high_j1_strip_index_bounded γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, ?_⟩
  intro δ hδ hδs
  have hδa' : δ < δa := lt_of_lt_of_le hδs (min_le_left _ _)
  have hδb' : δ < δb := lt_of_lt_of_le hδs (min_le_right _ _)
  obtain ⟨κ₀, hκ₀, hoff⟩ := hoff δ hδ hδa'
  obtain ⟨κ₁, hκ₁, hidx⟩ := hidx δ hδ hδb'
  refine ⟨min κ₀ κ₁, lt_min hκ₀ hκ₁, ?_⟩
  intro κ hκ hκs
  have hκs₀ : κ ≤ κ₀ := le_trans hκs (min_le_left _ _)
  have hκs₁ : κ ≤ κ₁ := le_trans hκs (min_le_right _ _)
  obtain ⟨N₀, hoff⟩ := hoff κ hκ hκs₀
  obtain ⟨N₁, hidx⟩ := hidx κ hκ hκs₁
  refine ⟨max N₀ N₁, ?_⟩
  intro N hN a ha b hb hphase
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN₁ : N₁ ≤ N := le_trans (le_max_right _ _) hN
  by_contra hcon
  push Not at hcon
  have hsmall := hoff N hN₀ a ha b hb (fun h hh => hcon h)
  exact absurd hsmall (not_le.mpr hphase)

end LeanLab.ExceptionalSet.Decomp553d
