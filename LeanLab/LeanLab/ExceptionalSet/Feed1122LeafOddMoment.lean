/-
Split of `leaf_odd_moment` of `SPLIT_lemma6`, display 30 of Brudern-Perelli 1998,
P0082, section 6, p. 367-369. The paper proves display 30 by the argument for display 29
with `W_e(α)` replaced by `W_o(α) = W_e(-α)`, p. 369. The kernel `W_o` equals `1` on
`[Δ/2, 1 - Δ/2]` and vanishes on `[-1, 0]`, so for `{F(n)}` in the same good range Lemma 1
returns `R₁(ν_n)` alone. The trivial bound and the Lemma 4 boundary count are shared with
display 29 and imported from `Feed1122LeafEvenMoment`, with the same choice
`Δ = ℰ^(-1/3) / (log X)²` explained there.

Leaves: `leaf_odd_good_moment`, HARD, here; `leaf_R1_trivial_bound` and
`leaf_boundary_count`, MEDIUM, in `Feed1122LeafEvenMoment`.
`leaf_odd_moment_of_leaves` restates `leaf_odd_moment` exactly and is proved from them.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.Feed1122LeafEvenMoment

namespace LeanLab.ExceptionalSet.U1539

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: display 30 of P0082, p. 369, on the good `n`, the cognate of displays 31, 32 and
35 to 39 with `W_o(α) = W_e(-α)`. For the `n` of the window with `ν_n` odd and
`{F(n)} ∈ [Δ/2, 1 - Δ/2]`, `Δ = ℰ^(-1/3) / (log X)²`, Lemma 1 with the kernel `K_o` gives
`R₁(ν_n)` as the major arc integral of `S² K_o e(-αF(n))`, and the tail removal, the opened
square and Lemma 9 with the reflected sum bound the second moment. Class HARD. It bounds a
sub-sum of the parent's sum only, so it is strictly weaker than `leaf_odd_moment`. -/
theorem leaf_odd_good_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter
              (fun n : ℕ => ¬ (Int.fract (F γ n) <
                  calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 ∨
                1 - calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 <
                  Int.fract (F γ n))),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- `leaf_odd_moment` of `SPLIT_lemma6`, statement unchanged, from the leaves. -/
theorem leaf_odd_moment_of_leaves (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hgood⟩ := leaf_odd_good_moment γ h1 h2
  obtain ⟨κb, hκb, hbad⟩ := leaf_boundary_count γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κa, hκa, hgood⟩ := hgood δ hδ hδs
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκle => ?_⟩
  obtain ⟨B₁, hB₁, N₁, hgood⟩ := hgood κ hκ (hκle.trans (min_le_left _ _))
  obtain ⟨B₂, hB₂, N₂, hbad⟩ := hbad κ hκ (hκle.trans (min_le_right _ _))
  refine ⟨B₁ + 8 * B₂, by linarith, max (max N₁ N₂) 3, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hL := (F_ge_two_and_log γ h1 N hN3).2
  have hΔ : 0 < calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 := by
    have : 0 < calE γ κ N := Real.exp_pos _
    have : 0 < Real.log (F γ N) := by linarith
    positivity
  exact branch_moment_assemble γ h1 (fun n : ℕ => ¬ Even (nu γ n)) (fun n => nu γ n)
    δ κ B₁ B₂ hB₂ N hN3 (hgood N hN1) (hbad N hN2 _ hΔ)

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.leaf_odd_moment_of_leaves
