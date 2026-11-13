import Mathlib
import LeanLab.ExceptionalSet.BrudernPerelli1998
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.UpJ200.DecompJ200

/-! Split of `DecompJ200.leaf_major_bound`, P0082 page 365 Lemma 8, second and third parts.

An existing file may not gain a `sorry`, so the two open steps of the major arc bound live here,
in the `UpJ200` cone that `DecompJ200` can import. The only definition of that file used below is
`window`, copied verbatim in `UpJ200/DecompJ200.lean`, so the leaves apply to the window of
`DecompJ200` by definition. `DecompJ200.leaf_major_bound` proves itself from these two leaves,
after the first part, the Fourier identity `leaf_major_identity`, which is proved there.

AI wrote this Lean code. Goldbach is open. -/

namespace LeanLab.ExceptionalSet.UpJ200.MajorBoundLeavesJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

attribute [local instance] Classical.propDecidable

/-- LEAF: P0082 page 358 Lemma 4, applied on page 364 after display (23). With `Δ = E^(-1/8)`, at
most `B N Δ` members of the window have `{F(n)} < Δ` or `{F(n)} > 1 - Δ`, for every small `κ`. -/
theorem leaf_major_fractional_boundary (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
            1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF: P0082 page 362 Lemma 7, with the odd second moment of pages 366 to 369 displays (29) and
(30): the real part of `R₁(ν_n) + R₁(ν_n + 1)` is below `c₀ X E^(-1/10)` for at most
`B N E^(-1/12)` members of the window. -/
theorem leaf_major_coefficient_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
              U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

end LeanLab.ExceptionalSet.UpJ200.MajorBoundLeavesJ200
