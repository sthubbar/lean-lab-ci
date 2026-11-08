import LeanLab.ExceptionalSet.SPLIT_leaf_fractional_boundary

/-!
Split of `SPLIT_leaf_fractional_boundary.leaf_boundary_inner_low`. The inner half
`Δ / 2 ≤ {F γ n} < Δ` of the lower fractional boundary arc, `Δ = calE γ κ N ^ (-(1 / 8))`,
is cut two ways at once: by the arc position inside the half (`Δ / 2 ≤ {F} < 3 Δ / 4` and
`3 Δ / 4 ≤ {F} < Δ`), and by the position of the index inside the window (`n ≤ 3 N / 4`
and `3 N / 4 < n`). That gives four block counts. The assembly reassembles the inner-half
count from them by a case split on the fractional part and on the index, using only that
the four pieces cover and that cardinalities are subadditive over a union.

No existing file is edited, and the assembly does not use the original leaf.
-/

namespace LeanLab.ExceptionalSet.Decomp371a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Sp eC majorArcs)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. Step 1 of the inner half of the lower boundary arc. The lower half of the inner
half, `Δ / 2 ≤ {F γ n} < 3 Δ / 4` with `Δ = calE γ κ N ^ (-(1 / 8))`, restricted to the
first block of window indices `n ≤ 3 N / 4`. Both restrictions cut the counted set down:
it is contained in the inner half of the lower boundary arc, so the estimate is strictly
weaker than the inner-half count. -/
theorem leaf_inner_low_first_block_low_arc (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ => n ≤ 3 * N / 4 ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < 3 * calE γ κ N ^ (-(1 / 8 : ℝ)) / 4)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 2. The upper half of the inner half of the lower boundary arc,
`3 Δ / 4 ≤ {F γ n} < Δ`, again restricted to the first block of window indices
`n ≤ 3 N / 4`. It is contained in the inner half of the lower boundary arc, so the
estimate is strictly weaker than the inner-half count. -/
theorem leaf_inner_low_first_block_high_arc (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ => n ≤ 3 * N / 4 ∧ 3 * calE γ κ N ^ (-(1 / 8 : ℝ)) / 4 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 3. The lower half of the inner half of the lower boundary arc,
`Δ / 2 ≤ {F γ n} < 3 Δ / 4`, restricted to the second block of window indices
`3 N / 4 < n`. It is contained in the inner half of the lower boundary arc, so the
estimate is strictly weaker than the inner-half count. -/
theorem leaf_inner_low_second_block_low_arc (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ => 3 * N / 4 < n ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < 3 * calE γ κ N ^ (-(1 / 8 : ℝ)) / 4)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 4. The upper half of the inner half of the lower boundary arc,
`3 Δ / 4 ≤ {F γ n} < Δ`, restricted to the second block of window indices
`3 N / 4 < n`. It is contained in the inner half of the lower boundary arc, so the
estimate is strictly weaker than the inner-half count. -/
theorem leaf_inner_low_second_block_high_arc (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ => 3 * N / 4 < n ∧ 3 * calE γ κ N ^ (-(1 / 8 : ℝ)) / 4 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- Assembly. The inner half of the lower boundary arc is covered by its four blocks: on each
index and each arc half, the two case splits together exhaust the inner-half condition, so the
inner-half count is at most the sum of the four block counts, and the four constants add. -/
theorem leaf_boundary_inner_low_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) : ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (((window γ N).filter (fun n : ℕ => calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κ1, hκ1, hb1⟩ := leaf_inner_low_first_block_low_arc γ h1 h2
  obtain ⟨κ2, hκ2, hb2⟩ := leaf_inner_low_first_block_high_arc γ h1 h2
  obtain ⟨κ3, hκ3, hb3⟩ := leaf_inner_low_second_block_low_arc γ h1 h2
  obtain ⟨κ4, hκ4, hb4⟩ := leaf_inner_low_second_block_high_arc γ h1 h2
  refine ⟨min (min κ1 κ2) (min κ3 κ4),
    lt_min (lt_min hκ1 hκ2) (lt_min hκ3 hκ4), fun κ hκ hκs => ?_⟩
  have hκ1' : κ ≤ κ1 := hκs.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hκ2' : κ ≤ κ2 := hκs.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hκ3' : κ ≤ κ3 := hκs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκ4' : κ ≤ κ4 := hκs.trans ((min_le_right _ _).trans (min_le_right _ _))
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
  let Δ : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let T := (window γ N).filter (fun n : ℕ =>
    Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)
  let A1 := (window γ N).filter (fun n : ℕ =>
    n ≤ 3 * N / 4 ∧ Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 3 * Δ / 4)
  let A2 := (window γ N).filter (fun n : ℕ =>
    n ≤ 3 * N / 4 ∧ 3 * Δ / 4 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)
  let A3 := (window γ N).filter (fun n : ℕ =>
    3 * N / 4 < n ∧ Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 3 * Δ / 4)
  let A4 := (window γ N).filter (fun n : ℕ =>
    3 * N / 4 < n ∧ 3 * Δ / 4 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)
  have hsub : T ⊆ A1 ∪ (A2 ∪ (A3 ∪ A4)) := by
    intro n hn
    simp only [T, A1, A2, A3, A4, Finset.mem_filter, Finset.mem_union] at hn ⊢
    obtain ⟨hnW, hlo, hhi⟩ := hn
    by_cases hw : n ≤ 3 * N / 4
    · by_cases ha : Int.fract (F γ n) < 3 * Δ / 4
      · exact Or.inl ⟨hnW, hw, hlo, ha⟩
      · exact Or.inr (Or.inl ⟨hnW, hw, le_of_not_gt ha, hhi⟩)
    · have hw' : 3 * N / 4 < n := lt_of_not_ge hw
      by_cases ha : Int.fract (F γ n) < 3 * Δ / 4
      · exact Or.inr (Or.inr (Or.inl ⟨hnW, hw', hlo, ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hnW, hw', le_of_not_gt ha, hhi⟩))
  have hcard : T.card ≤ A1.card + (A2.card + (A3.card + A4.card)) := by
    have h1' := Finset.card_le_card hsub
    have h2' := Finset.card_union_le A1 (A2 ∪ (A3 ∪ A4))
    have h3' := Finset.card_union_le A2 (A3 ∪ A4)
    have h4' := Finset.card_union_le A3 A4
    omega
  have e1 : (A1.card : ℝ) ≤ B1 * N * Δ := hN1 N hN1'
  have e2 : (A2.card : ℝ) ≤ B2 * N * Δ := hN2 N hN2'
  have e3 : (A3.card : ℝ) ≤ B3 * N * Δ := hN3 N hN3'
  have e4 : (A4.card : ℝ) ≤ B4 * N * Δ := hN4 N hN4'
  have hsum : (T.card : ℝ) ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) + (A4.card : ℝ) := by
    have hcast : ((T.card : ℕ) : ℝ) ≤
        ((A1.card + (A2.card + (A3.card + A4.card)) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at hcast
    linarith
  calc (T.card : ℝ) ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) + (A4.card : ℝ) := hsum
    _ ≤ B1 * N * Δ + B2 * N * Δ + B3 * N * Δ + B4 * N * Δ := by linarith
    _ = (B1 + B2 + B3 + B4) * N * Δ := by ring

end LeanLab.ExceptionalSet.Decomp371a
