import LeanLab.ExceptionalSet.SPLIT_leaf_fractional_boundary

/-!
Split of the first arc of `Decomp371a.leaf_fractional_boundary`: the outer half of the lower
boundary arc, the window indices whose fractional part satisfies
`{F γ n} < Δ / 2`, where `Δ = calE γ κ N ^ (-(1 / 8))`.

The band is cut at the quarter point `Δ / 4` into a lower and an upper piece, and the window
`n ≤ 2N` is cut at the index `N` into the indices `n ≤ N` and the indices `N < n`. The four
resulting pieces are counted separately. Every piece adds one genuine restriction to the
condition defining the band, either an index restriction or the refinement of the fractional
part condition, so each booked estimate is an estimate for a subset of the band and is strictly
easier than the estimate for the band itself.

`Δ > 0` holds because `Δ` is a positive power of the exponential `calE`, so `Δ / 4 < Δ / 2` and
the lower piece of the band is contained in it.

The assembly `leaf_boundary_outer_low_split` adds the four constants, takes the largest of the
four thresholds and the smallest of the four caps, and reproduces the statement of the arc
exactly. It uses only the four leaves below; the sealed statement of the arc is used nowhere.

The four leaves are open; the assembly is complete.
-/

namespace LeanLab.ExceptionalSet.Decomp371a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Sp eC majorArcs)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. Step 1 of the split: the lower piece of the band, on the indices `n ≤ N`. It counts the
window indices with `n ≤ N` and `{F γ n} < Δ / 4`, where `Δ = calE γ κ N ^ (-(1 / 8))`.
Since `Δ > 0` we have `Δ / 4 < Δ / 2`, so every index counted here satisfies the band condition
`{F γ n} < Δ / 2`; with `n ≤ N` added, the counted set is a subset of the band and the estimate is
strictly easier than the band estimate. -/
theorem leaf_outer_low_low_band_lower_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          n ≤ N ∧ Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 4)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 2 of the split: the upper piece of the band, on the indices `n ≤ N`. It counts the
window indices with `n ≤ N` and `Δ / 4 ≤ {F γ n} < Δ / 2`, where
`Δ = calE γ κ N ^ (-(1 / 8))`. The condition on the fractional part is one half of the band
condition, and `n ≤ N` is added, so the counted set is a subset of the band and the estimate is
strictly easier than the band estimate. -/
theorem leaf_outer_low_high_band_lower_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          n ≤ N ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) / 4 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 3 of the split: the lower piece of the band, on the indices `N < n`. It counts the
window indices with `N < n` and `{F γ n} < Δ / 4`, where `Δ = calE γ κ N ^ (-(1 / 8))`.
As in step 1 the quarter point condition implies the band condition because `Δ > 0`, and `N < n`
is added, so the counted set is a subset of the band and the estimate is strictly easier than the
band estimate. -/
theorem leaf_outer_low_low_band_upper_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 4)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 4 of the split: the upper piece of the band, on the indices `N < n`. It counts the
window indices with `N < n` and `Δ / 4 ≤ {F γ n} < Δ / 2`, where
`Δ = calE γ κ N ^ (-(1 / 8))`. The condition on the fractional part is one half of the band
condition, and `N < n` is added, so the counted set is a subset of the band and the estimate is
strictly easier than the band estimate. -/
theorem leaf_outer_low_high_band_upper_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) / 4 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- Assembly. The band estimate follows from the four piece estimates: the band is covered by the
two quarter pieces crossed with the two index ranges, cardinalities are subadditive over that
cover, and the four constants, the four thresholds and the four caps combine. -/
theorem leaf_boundary_outer_low_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κ1, hκ1, hb1⟩ := leaf_outer_low_low_band_lower_indices γ h1 h2
  obtain ⟨κ2, hκ2, hb2⟩ := leaf_outer_low_high_band_lower_indices γ h1 h2
  obtain ⟨κ3, hκ3, hb3⟩ := leaf_outer_low_low_band_upper_indices γ h1 h2
  obtain ⟨κ4, hκ4, hb4⟩ := leaf_outer_low_high_band_upper_indices γ h1 h2
  refine ⟨min κ1 (min κ2 (min κ3 κ4)),
    lt_min hκ1 (lt_min hκ2 (lt_min hκ3 hκ4)), fun κ hκ hκs => ?_⟩
  have hκ1' : κ ≤ κ1 := hκs.trans (min_le_left _ _)
  have hκ2' : κ ≤ κ2 := hκs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκ3' : κ ≤ κ3 :=
    hκs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hκ4' : κ ≤ κ4 :=
    hκs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨B1, hB1, N1, hN1⟩ := hb1 κ hκ hκ1'
  obtain ⟨B2, hB2, N2, hN2⟩ := hb2 κ hκ hκ2'
  obtain ⟨B3, hB3, N3, hN3⟩ := hb3 κ hκ hκ3'
  obtain ⟨B4, hB4, N4, hN4⟩ := hb4 κ hκ hκ4'
  refine ⟨B1 + B2 + B3 + B4, by positivity, max N1 (max N2 (max N3 N4)), fun N hN => ?_⟩
  have hN1' : N1 ≤ N := (le_max_left N1 (max N2 (max N3 N4))).trans hN
  have hN2' : N2 ≤ N :=
    (le_max_left N2 (max N3 N4)).trans ((le_max_right N1 (max N2 (max N3 N4))).trans hN)
  have hN3' : N3 ≤ N :=
    (le_max_left N3 N4).trans ((le_max_right N2 (max N3 N4)).trans
      ((le_max_right N1 (max N2 (max N3 N4))).trans hN))
  have hN4' : N4 ≤ N :=
    (le_max_right N3 N4).trans ((le_max_right N2 (max N3 N4)).trans
      ((le_max_right N1 (max N2 (max N3 N4))).trans hN))
  set Δ : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let A := (window γ N).filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2)
  let L1 := (window γ N).filter (fun n : ℕ => n ≤ N ∧ Int.fract (F γ n) < Δ / 4)
  let R1 := (window γ N).filter (fun n : ℕ =>
    n ≤ N ∧ Δ / 4 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ / 2)
  let L2 := (window γ N).filter (fun n : ℕ => N < n ∧ Int.fract (F γ n) < Δ / 4)
  let R2 := (window γ N).filter (fun n : ℕ =>
    N < n ∧ Δ / 4 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ / 2)
  have hsub : A ⊆ L1 ∪ (R1 ∪ (L2 ∪ R2)) := by
    intro n hn
    simp only [A, L1, R1, L2, R2, Finset.mem_filter, Finset.mem_union] at hn ⊢
    obtain ⟨hnW, hf⟩ := hn
    by_cases hnN : n ≤ N
    · by_cases hq : Int.fract (F γ n) < Δ / 4
      · exact Or.inl ⟨hnW, hnN, hq⟩
      · exact Or.inr (Or.inl ⟨hnW, hnN, le_of_not_gt hq, hf⟩)
    · have hnN' : N < n := Nat.lt_of_not_le hnN
      by_cases hq : Int.fract (F γ n) < Δ / 4
      · exact Or.inr (Or.inr (Or.inl ⟨hnW, hnN', hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hnW, hnN', le_of_not_gt hq, hf⟩))
  have hcard : A.card ≤ L1.card + (R1.card + (L2.card + R2.card)) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le L1 (R1 ∪ (L2 ∪ R2))
    have h3 := Finset.card_union_le R1 (L2 ∪ R2)
    have h4 := Finset.card_union_le L2 R2
    omega
  have hA1 : (L1.card : ℝ) ≤ B1 * N * Δ := hN1 N hN1'
  have hA2 : (R1.card : ℝ) ≤ B2 * N * Δ := hN2 N hN2'
  have hA3 : (L2.card : ℝ) ≤ B3 * N * Δ := hN3 N hN3'
  have hA4 : (R2.card : ℝ) ≤ B4 * N * Δ := hN4 N hN4'
  have hsum : (A.card : ℝ) ≤
      (L1.card : ℝ) + (R1.card : ℝ) + (L2.card : ℝ) + (R2.card : ℝ) := by
    have := hcard
    have hcast : (A.card : ℝ) ≤ ((L1.card + (R1.card + (L2.card + R2.card)) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hcast
    linarith
  have hgoal : (A.card : ℝ) ≤ (B1 + B2 + B3 + B4) * N * Δ := by
    calc (A.card : ℝ) ≤ (L1.card : ℝ) + (R1.card : ℝ) + (L2.card : ℝ) + (R2.card : ℝ) := hsum
      _ ≤ B1 * N * Δ + B2 * N * Δ + B3 * N * Δ + B4 * N * Δ := by linarith
      _ = (B1 + B2 + B3 + B4) * N * Δ := by ring
  exact hgoal

end LeanLab.ExceptionalSet.Decomp371a
