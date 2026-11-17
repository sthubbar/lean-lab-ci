import LeanLab.ExceptionalSet.SPLIT_leaf_inner_high_j0

/-!
Split of `leaf_high_j0_large_phase_strip` from the split file of the assigned
upper index block of the half interval.

The target says: for `γ` in `(1, 3 / 2)` there is a width `δ₀` and, for each
smaller positive `δ` and each `κ` below a positive cap, an eventual threshold
`N₀` such that on the truncated minor window every pair of points whose assigned
block phase exceeds `N E ^ (-(5 / 6))` differs by a point that lies in the
finite union of half integer strips of radius `X ^ (δ - 1)` around multiples of
one half.

The step is cut into the two inputs its argument actually needs.

  * `leaf_high_j0_off_lattice_block_small` is the smallness of the block phase
    away from the half integer lattice: off the strips of radius `X ^ (δ - 1)`
    around the half integers with index at most `E ^ (3 / 4)` the restricted
    block sum is at most `N E ^ (-(5 / 6))`. It is one inequality about one sum,
    it has no existential conclusion and no statement about the strips as a set,
    so it is strictly weaker than the target: it is the contrapositive of the
    target on the finitely many half integers that can occur.
  * `leaf_high_j0_strip_index_bounded` is the arithmetic of that finite range:
    two points of the truncated window are at distance at most `2 E ^ (2 / 3)`
    and the strip radius is at most one once the threshold is passed, so an
    integer within `X ^ (δ - 1)` of their difference is bounded by
    `E ^ (3 / 4)`. This carries no phase and no sum.

The assembly is pure logic plus the ready-made finite index range: if `b` is not
in the union of strips, every bounded half integer is off the strips, the first
step bounds the block phase by `N E ^ (-(5 / 6))`, and this contradicts the
largeness hypothesis.

No existing file is edited, and the assembly does not use the target theorem.
-/

namespace LeanLab.ExceptionalSet.Decomp553b

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- LEAF. Step one, the block phase is small off the half integer strips. For
every admissible width `δ` and every admissible cap for `κ` there is an eventual
threshold such that, at every point `a` and every point `b` of the truncated
minor window, if `b - a` is further than `X ^ (δ - 1)` from `h / 2` for every
integer `h` with `|h| ≤ E ^ (3 / 4)`, then the assigned block phase at `b - a` is
at most `N E ^ (-(5 / 6))`. This is one inequality about one block sum, with no
existential conclusion and no set membership: it is the localization content of
the target read in contrapositive form on a bounded range of half integers, hence
strictly weaker. -/
theorem leaf_high_j0_off_lattice_block_small (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  sorry

/-- LEAF. Step two, the strip index is bounded. Two points of the truncated minor
window differ by at most `2 E ^ (2 / 3)`, the strip radius is at most one, and
`4 E ^ (2 / 3) + 2 ≤ E ^ (3 / 4)` eventually; hence any integer `h` with
`|(b - a) - h / 2| ≤ X ^ (δ - 1)` satisfies `|h| ≤ E ^ (3 / 4)`. This is one
inequality between real numbers: it involves neither the block phase nor any
sum, so it is strictly weaker than the target. -/
theorem leaf_high_j0_strip_index_bounded (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              ∀ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) →
                (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) := by
  sorry

/-- Assembly. The two steps above localize the large values of the assigned
block phase into the finite union of strips. Suppose `b` is outside the union.
Then every half integer index of the bounded range carries a point of the union
away from `b`, which by the first step bounds the block phase by
`N E ^ (-(5 / 6))`, contradicting largeness. The index range is the ready-made
finite set of half integers of size at most `E ^ (3 / 4)`, which the second step
supplies. -/
theorem leaf_high_j0_large_phase_strip_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ →
              b ∈ strips (calE γ κ N) (F γ N) δ a := by
  obtain ⟨δa, hδa, hoff⟩ := leaf_high_j0_off_lattice_block_small γ h1 h2
  obtain ⟨δb, hδb, hidx⟩ := leaf_high_j0_strip_index_bounded γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, ?_⟩
  intro δ hδ hδs
  have hδa' : δ < δa := hδs.trans_le (min_le_left _ _)
  have hδb' : δ < δb := hδs.trans_le (min_le_right _ _)
  obtain ⟨κa, hκa, hoff⟩ := hoff δ hδ hδa'
  obtain ⟨κb, hκb, hidx⟩ := hidx δ hδ hδb'
  refine ⟨min κa κb, lt_min hκa hκb, ?_⟩
  intro κ hκ hκs
  have hκa' : κ ≤ κa := hκs.trans (min_le_left _ _)
  have hκb' : κ ≤ κb := hκs.trans (min_le_right _ _)
  obtain ⟨Na, hoff⟩ := hoff κ hκ hκa'
  obtain ⟨Nb, hidx⟩ := hidx κ hκ hκb'
  refine ⟨max Na Nb, ?_⟩
  intro N hN
  have hNa : Na ≤ N := (le_max_left _ _).trans hN
  have hNb : Nb ≤ N := (le_max_right _ _).trans hN
  intro a ha b hb hlarge
  by_contra hnot
  have hoffl : ∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
      F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2| := by
    intro h hh
    apply not_le.mp
    intro hle
    apply hnot
    refine Set.mem_iUnion₂.mpr ⟨h, mem_stripIndices (calE γ κ N) h hh, ?_⟩
    rw [Set.mem_Icc]
    have habs := abs_le.mp hle
    constructor <;> linarith [habs.1, habs.2]
  have hsmall := hoff N hNa a ha b hb hoffl
  exact absurd hsmall (not_le.mpr hlarge)

end LeanLab.ExceptionalSet.Decomp553b
