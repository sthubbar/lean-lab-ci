import LeanLab.ExceptionalSet.Decomp371a

/-!
Split of `Decomp371a.leaf_fractional_boundary`. The two boundary arcs of the fractional part,
`{F γ n} < Δ` and `1 - Δ < {F γ n}` with `Δ = calE γ κ N ^ (-(1 / 8))`, are each cut into an
outer and an inner half, giving four one-sided count estimates. The assembly reassembles the
two-arc count from them by a case split on the fractional part and a cardinality bound, and
reproduces the sealed statement exactly.

No existing file is edited, and the assembly does not use the original leaf.
-/

namespace LeanLab.ExceptionalSet.Decomp371a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Sp eC majorArcs)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. Step 1 of the boundary split: the outer half of the lower boundary arc, the window
indices with `{F γ n} < Δ / 2` where `Δ = calE γ κ N ^ (-(1 / 8))`, number at most `B N Δ`
eventually. Because `Δ / 2 < Δ`, this set is contained in the lower boundary arc itself, so the
estimate is strictly weaker than the two-arc boundary count. -/
theorem leaf_boundary_outer_low (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 2 of the boundary split: the inner half of the lower boundary arc, the window
indices with `Δ / 2 ≤ {F γ n} < Δ`. It is contained in the lower boundary arc, so the estimate is
strictly weaker than the two-arc boundary count. -/
theorem leaf_boundary_inner_low (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 3 of the boundary split: the inner half of the upper boundary arc, the window
indices with `1 - Δ < {F γ n} ≤ 1 - Δ / 2`. It is contained in the upper boundary arc, so the
estimate is strictly weaker than the two-arc boundary count. -/
theorem leaf_boundary_inner_high (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n) ∧
            Int.fract (F γ n) ≤ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 4 of the boundary split: the outer half of the upper boundary arc, the window
indices with `1 - Δ / 2 < {F γ n}`. Since `Δ / 2 < Δ` it is contained in the upper boundary arc,
so the estimate is strictly weaker than the two-arc boundary count. -/
theorem leaf_boundary_outer_high (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- Assembly. The two-arc fractional boundary count follows from the four half-arc counts: the
boundary set is the union of the four pieces, cardinalities add, and the four constants add. -/
theorem leaf_fractional_boundary_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
            1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κ1, hκ1, hb1⟩ := leaf_boundary_outer_low γ h1 h2
  obtain ⟨κ2, hκ2, hb2⟩ := leaf_boundary_inner_low γ h1 h2
  obtain ⟨κ3, hκ3, hb3⟩ := leaf_boundary_inner_high γ h1 h2
  obtain ⟨κ4, hκ4, hb4⟩ := leaf_boundary_outer_high γ h1 h2
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
  let Δ : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let T := (window γ N).filter (fun n : ℕ =>
    Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))
  let A1 := (window γ N).filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2)
  let A2 := (window γ N).filter (fun n : ℕ =>
    Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)
  let A3 := (window γ N).filter (fun n : ℕ =>
    1 - Δ < Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ / 2)
  let A4 := (window γ N).filter (fun n : ℕ => 1 - Δ / 2 < Int.fract (F γ n))
  have hsub : T ⊆ A1 ∪ (A2 ∪ (A3 ∪ A4)) := by
    intro n hn
    simp only [T, Finset.mem_filter] at hn
    obtain ⟨hnW, hcond⟩ := hn
    by_cases ha : Int.fract (F γ n) < Δ / 2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnW, ha⟩)
    · rcases hcond with hlow | hhigh
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hnW, le_of_not_gt ha, hlow⟩))
      · by_cases hb : Int.fract (F γ n) ≤ 1 - Δ / 2
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnW, hhigh, hb⟩)))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnW, lt_of_not_ge hb⟩)))
  have hcard : T.card ≤ A1.card + (A2.card + (A3.card + A4.card)) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le A1 (A2 ∪ (A3 ∪ A4))
    have h3 := Finset.card_union_le A2 (A3 ∪ A4)
    have h4 := Finset.card_union_le A3 A4
    omega
  have hA1 : (A1.card : ℝ) ≤ B1 * N * Δ := hN1 N hN1'
  have hA2 : (A2.card : ℝ) ≤ B2 * N * Δ := hN2 N hN2'
  have hA3 : (A3.card : ℝ) ≤ B3 * N * Δ := hN3 N hN3'
  have hA4 : (A4.card : ℝ) ≤ B4 * N * Δ := hN4 N hN4'
  have hsum : (T.card : ℝ) ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) + (A4.card : ℝ) := by
    have := hcard
    have hcast : (T.card : ℝ) ≤ ((A1.card + (A2.card + (A3.card + A4.card)) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hcast
    linarith
  calc (T.card : ℝ) ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) + (A4.card : ℝ) := hsum
    _ ≤ B1 * N * Δ + B2 * N * Δ + B3 * N * Δ + B4 * N * Δ := by linarith
    _ = (B1 + B2 + B3 + B4) * N * Δ := by ring

end LeanLab.ExceptionalSet.Decomp371a
