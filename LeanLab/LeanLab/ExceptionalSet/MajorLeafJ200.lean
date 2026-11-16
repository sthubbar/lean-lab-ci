import Mathlib
import LeanLab.ExceptionalSet.BrudernPerelli1998
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.CoeffSupplyJ200

/-!
Upstream home of the two open leaves of the major arc split of `DecompJ200.leaf_major_bound`.
Source: P0082, Bruedern and Perelli 1998, https://doi.org/10.5802/aif.1621, page 362 Lemma 6 and
the proof of Lemma 7 on pages 362 to 364, with displays (29) and (30) on pages 366 to 369.

`DecompJ200.lean` proves `leaf_major_coefficient_lower` from exactly these two theorems, so both
must sit in a module that `DecompJ200` can import. `window` below is a copy of `DecompJ200.window`,
character for character, so that the two statements are the ones `DecompJ200` uses.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.MajorLeafJ200

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998
open LeanLab.ExceptionalSet.U1539 (nu nuOdd calE)

/-- Copy of `DecompJ200.window`, the window of section 5, p. 366: `n <= 2N` with `X/2 < nu_n`,
`X = F(N)`. -/
noncomputable def window (gamma : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => F gamma N / 2 < nu gamma n ∧ (nu gamma n : ℝ) ≤ F gamma N)

/-- LEAF: P0082 page 362, proof of Lemma 7, cases (i) to (iii) on pages 362 to 364: "In view of
Lemma 6 it suffices to show that `R₁(ν_n^e) ≫ X ℰ^{-1/10}` for all but `O(N ℰ^{-1/12})` values
of `n` in the relevant range", with `ν_n^e` the even one of `ν_n, ν_n + 1`. Downstream,
`Decomp467b.even_coefficient_from_inputs` proves this statement CONDITIONAL ON the cited Lemma 4
and the pointwise character case input `hpoint`; it cannot be imported here. -/
theorem leaf_major_even_coefficient (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (CoeffSupplyJ200.evenAdjacent γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- LEAF: P0082 page 362 Lemma 6, in the second moment form that its proof in section 7 establishes,
pages 366 to 369 displays (29) and (30): `Σ_n |R₁(ν°_n)|² ≪ N X² ℰ^{-1/3}` over the window.
The same statement is the hypothesis `hodd` of `Decomp467b.coefficient_lower_from_inputs` and the
conclusion of `OddMoment446.odd_moment_uniform`, which is CONDITIONAL ON the two parity moments
`Decomp371c.leaf_even_moment` and `Decomp371c.leaf_odd_moment`; neither can be imported here. -/
theorem leaf_major_odd_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N,
            ‖U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (U1539.nuOdd γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry
