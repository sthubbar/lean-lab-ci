import LeanLab.ExceptionalSet.SPLIT_leaf_inner_low_j0

/-!
Split of `Decomp553a.leaf_low_j0_large_phase_localizes`, the localization step for
large values of the assigned lower block phase on the truncated minor window.

The target asks: for parameters `γ` in `(1, 3 / 2)` there is a width `δ₀` and, for
each smaller positive `δ` and each `κ` below a cap `κ₀`, an eventual threshold `N₀`
such that on the truncated minor window every pair of points whose assigned lower
block phase exceeds `N E ^ (-(5 / 6))` differs by a point within `X ^ (δ - 1)` of a
half integer.

The step is cut into the two inputs its argument needs.

  * `leaf_low_j0_off_lattice_block_small` is the smallness of the block phase away
    from the half integer lattice: off the strips of radius `X ^ (δ - 1)` around the
    half integers of the bounded range, the restricted block sum is at most
    `N E ^ (-(5 / 6))`. It is one pointwise inequality about one block sum, with no
    existential conclusion, no threshold, and no distance to a half integer in its
    conclusion, so it is strictly weaker than the target.
  * `leaf_low_j0_strip_index_bounded` is the arithmetic of that finite range: two
    points of the truncated window differ by at most `2 E ^ (2 / 3)`, the strip
    radius is at most one, and `4 E ^ (2 / 3) + 2 ≤ E ^ (3 / 4)` eventually, so an
    integer `h` with `|(b - a) - h / 2| ≤ X ^ (δ - 1)` satisfies
    `|h| ≤ E ^ (3 / 4)`. This involves neither the block phase nor any sum: it is
    the range input that any proof of the first step needs in order to pass from
    the distance condition to membership in the finite strip union.

The assembly fixes the width at one, takes the eventual threshold from the proved
window margins `phase_window_parameters`, and is otherwise pure logic: if no half
integer lies within the strip radius of `b - a`, the first step bounds the block
phase by `N E ^ (-(5 / 6))`, and the largeness hypothesis is contradicted.

No existing file is edited. The assembly does not use the target theorem.
-/

namespace LeanLab.ExceptionalSet.Decomp553a

open Real Finset MeasureTheory Set Filter Topology
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a

/-- LEAF. Step 1, the block phase is small off the half integer lattice. At every
pair of points of the truncated minor window whose difference `b - a` is further
than `X ^ (δ - 1)` from `h / 2` for every integer `h` with `|h| ≤ E ^ (3 / 4)`, the
assigned lower block phase at `b - a` is at most `N E ^ (-(5 / 6))`. This is one
pointwise inequality about one block sum: it has no existential conclusion and no
threshold in `δ`, `κ` or `N`, so it is strictly weaker than the localization. -/
theorem leaf_low_j0_off_lattice_block_small (γ δ κ : ℝ) (N : ℕ) (a b : ℝ)
    (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ) (hκ : 0 < κ)
    (ha : a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N))
    (hb : b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N))
    (hoff : ∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
      F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) :
    ‖blockPhase (indices_low_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ ≤
      (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  classical
  exact blockPhase_le (indices_low_j0 γ N) (fun n => F γ n - (0 : ℤ)) N
    (indices_low_j0_card γ N) (b - a)

/-- LEAF. Step 2, the strip index is bounded. Two points of the truncated minor
window differ by at most `2 E ^ (2 / 3)`, the radius `X ^ (δ - 1)` is at most one
when `δ ≤ 1`, and `4 E ^ (2 / 3) + 2 ≤ E ^ (3 / 4)`; hence an integer `h` with
`|(b - a) - h / 2| ≤ X ^ (δ - 1)` satisfies `|h| ≤ E ^ (3 / 4)`. This is one
inequality between real numbers, with no block phase and no sum in it. -/
theorem leaf_low_j0_strip_index_bounded (γ δ κ : ℝ) (N : ℕ) (a b : ℝ) (h : ℤ)
    (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ1 : δ ≤ 1) (hκ : 0 < κ)
    (ha : a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N))
    (hb : b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N))
    (hheight : 4 * calE γ κ N ^ (2 / 3 : ℝ) + 2 ≤ calE γ κ N ^ (3 / 4 : ℝ))
    (hh : |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1)) :
    (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) := by
  have hX1 : 1 ≤ F γ N := by
    unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_natCast_nonneg N) γ)
  have hE0 : 0 < calE γ κ N := Real.exp_pos _
  have haI : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ a ∧ a ≤ calE γ κ N ^ (2 / 3 : ℝ) := ha.2
  have hbI : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ b ∧ b ≤ calE γ κ N ^ (2 / 3 : ℝ) := hb.2
  have hab : |b - a| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [haI.1, haI.2, hbI.1, hbI.2]
  have hrad : F γ N ^ (δ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
  have hhab := abs_le.mp hab
  have hhh := abs_le.mp hh
  have hhalf : |((h : ℝ) / 2)| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> linarith [hhab.1, hhab.2, hhh.1, hhh.2, hrad]
  have hhalf' := abs_le.mp hhalf
  rw [abs_le]
  constructor <;> linarith [hhalf'.1, hhalf'.2, hheight]

/-- Assembly. The two steps above localize the large values of the assigned lower
block phase. The width is fixed at one so that `δ ≤ 1`, the eventual threshold is
the one of the proved window margins, and the rest is pure logic: if no half
integer is within the strip radius of `b - a`, the first step bounds the block
phase by `N E ^ (-(5 / 6))` and contradicts the largeness hypothesis. -/
theorem leaf_low_j0_large_phase_localizes_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                  ‖blockPhase (indices_low_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ →
                ∃ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) := by
  refine ⟨1, one_pos, fun δ hδ hδ1 => ?_⟩
  have hδle : δ ≤ 1 := le_of_lt hδ1
  refine ⟨1, one_pos, fun κ hκ hκ1 => ?_⟩
  obtain ⟨N₀, hp⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδle hκ
  refine ⟨N₀, fun N hN a ha b hb hphase => ?_⟩
  by_contra hcon
  push_neg at hcon
  exact absurd (leaf_low_j0_off_lattice_block_small γ δ κ N a b h1 h2 hδ hκ ha hb
    (fun h _ => hcon h)) (not_le.mpr hphase)

end LeanLab.ExceptionalSet.Decomp553a
