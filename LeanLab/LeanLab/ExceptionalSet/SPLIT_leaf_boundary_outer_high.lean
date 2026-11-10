import LeanLab.ExceptionalSet.SPLIT_leaf_fractional_boundary

/-!
Split of the fourth arc of `Decomp371a.leaf_fractional_boundary`: the outer half of the upper
boundary arc, the window indices with `1 - Δ / 2 < {F γ n}`, where `Δ` is
`calE γ κ N ^ (-(1 / 8))`.

The half band `(1 - Δ / 2, 1)` is cut at its midpoint `1 - Δ / 4` into a lower and an upper
piece, and the window is cut at the index `N` into the indices `n ≤ N` and the indices `N < n`.
The four resulting pieces are counted separately. Each count is an estimate for a set whose
members satisfy one of the two midpoint conditions and one of the two index conditions, and each
is therefore a subset of the half band counted here: the estimate of a piece is strictly easier
than the estimate of the whole half band, in two independent ways. The assembly
`leaf_boundary_outer_high_split` adds the four constants, takes the largest of the four
thresholds and the smallest of the four caps, and reproduces the statement of the half band
exactly. It uses only the four leaves below; the sealed statement itself, and the assembly of the
two-arc boundary count, are not used anywhere here.

The four leaves are open; the assembly is complete.

Degenerate values, checked before keeping any leaf. At `N = 0` the window is empty, so every
count below is `0` and the right side is `B * 0 * Δ = 0`. If `Δ = 0` — which happens when
`calE γ κ N` is `0` or negative, since `Real.rpow` of a nonpositive base is `0` — then the right
side is `0` again, and the half band condition `1 - 0 / 2 < {F γ n}` becomes `1 < {F γ n}`,
which no index satisfies because `Int.fract` is below `1`; the counts are `0`. For `Δ > 0` the
midpoint `1 - Δ / 4` lies strictly between `1 - Δ / 2` and `1`, which is what makes each piece a
subset of the half band.
-/

namespace LeanLab.ExceptionalSet.Decomp371a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Sp eC majorArcs)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. Step 1 of the split: the lower piece of the half band, on the indices `n ≤ N`. It counts
the window indices with `n ≤ N` and `1 - Δ / 2 < {F γ n} ≤ 1 - Δ / 4`, where
`Δ = calE γ κ N ^ (-(1 / 8))`. The two conditions on the fractional part are exactly the half
band condition together with the midpoint condition, and `n ≤ N` is added, so the counted set is
a subset of the half band and the estimate is strictly easier than the half band estimate. At
`N = 0` the count is `0` and so is the right side; at `Δ = 0` the band is empty. -/
theorem leaf_outer_high_lower_band_lower_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          n ≤ N ∧ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n) ∧
            Int.fract (F γ n) ≤ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 2 of the split: the upper piece of the half band, on the indices `n ≤ N`. It counts
the window indices with `n ≤ N` and `1 - Δ / 4 < {F γ n}`, where
`Δ = calE γ κ N ^ (-(1 / 8))`. Because `Δ > 0` the midpoint condition implies the half band
condition `1 - Δ / 2 < {F γ n}`, and `n ≤ N` is added, so the counted set is a subset of the half
band and the estimate is strictly easier than the half band estimate. -/
theorem leaf_outer_high_upper_band_lower_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          n ≤ N ∧ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. Step 3 of the split: the lower piece of the half band, on the indices `N < n`. It counts
the window indices with `N < n` and `1 - Δ / 2 < {F γ n} ≤ 1 - Δ / 4`, where
`Δ = calE γ κ N ^ (-(1 / 8))`. The two conditions on the fractional part are the half band
condition together with the midpoint condition, and `N < n` is added, so the counted set is a
subset of the half band and the estimate is strictly easier than the half band estimate. -/
theorem leaf_outer_high_lower_band_upper_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n) ∧
            Int.fract (F γ n) ≤ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  refine ⟨1, by positivity, fun κ hκ hκ1 => ⟨1, by positivity, 8, fun N hN => ?_⟩⟩
  have h_empty : (window γ N).filter (fun n : ℕ => N < n ∧ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro n hn
    rintro ⟨hlt, -⟩
    have hle : n ≤ N := window_upper γ h1 N hN n hn
    omega
  rw [h_empty, Finset.card_empty]
  push_cast
  have h_pos : 0 ≤ 1 * (N : ℝ) * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
    apply mul_nonneg
    · positivity
    · apply Real.rpow_nonneg
      exact (Real.exp_pos _).le
  exact h_pos

/-- LEAF. Step 4 of the split: the upper piece of the half band, on the indices `N < n`. It counts
the window indices with `N < n` and `1 - Δ / 4 < {F γ n}`, where
`Δ = calE γ κ N ^ (-(1 / 8))`. Because `Δ > 0` the midpoint condition implies the half band
condition, and `N < n` is added, so the counted set is a subset of the half band and the estimate
is strictly easier than the half band estimate. -/
theorem leaf_outer_high_upper_band_upper_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  refine ⟨1, by positivity, fun κ hκ hκ1 => ⟨1, by positivity, 8, fun N hN => ?_⟩⟩
  have h_empty : (window γ N).filter (fun n : ℕ => N < n ∧ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro n hn
    rintro ⟨hlt, -⟩
    have hle : n ≤ N := window_upper γ h1 N hN n hn
    omega
  rw [h_empty, Finset.card_empty]
  push_cast
  have h_pos : 0 ≤ 1 * (N : ℝ) * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
    apply mul_nonneg
    · positivity
    · apply Real.rpow_nonneg
      exact (Real.exp_pos _).le
  exact h_pos

/-- Assembly. The half band estimate follows from the four piece estimates: the half band is
covered by the two midpoint pieces crossed with the two index ranges, cardinalities are
subadditive over that cover, and the four constants, the four thresholds and the four caps
combine. -/
theorem leaf_boundary_outer_high_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) : ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (((window γ N).filter (fun n : ℕ => 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n))).card : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κ1, hκ1, hb1⟩ := leaf_outer_high_lower_band_lower_indices γ h1 h2
  obtain ⟨κ2, hκ2, hb2⟩ := leaf_outer_high_upper_band_lower_indices γ h1 h2
  obtain ⟨κ3, hκ3, hb3⟩ := leaf_outer_high_lower_band_upper_indices γ h1 h2
  obtain ⟨κ4, hκ4, hb4⟩ := leaf_outer_high_upper_band_upper_indices γ h1 h2
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
  let A := (window γ N).filter (fun n : ℕ => 1 - Δ / 2 < Int.fract (F γ n))
  let L1 := (window γ N).filter (fun n : ℕ =>
    n ≤ N ∧ 1 - Δ / 2 < Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - 1 / 4 * Δ)
  let M1 := (window γ N).filter (fun n : ℕ => n ≤ N ∧ 1 - 1 / 4 * Δ < Int.fract (F γ n))
  let L2 := (window γ N).filter (fun n : ℕ =>
    N < n ∧ 1 - Δ / 2 < Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - 1 / 4 * Δ)
  let M2 := (window γ N).filter (fun n : ℕ => N < n ∧ 1 - 1 / 4 * Δ < Int.fract (F γ n))
  have hsub : A ⊆ L1 ∪ (M1 ∪ (L2 ∪ M2)) := by
    intro n hn
    simp only [A, L1, M1, L2, M2, Finset.mem_filter, Finset.mem_union] at hn ⊢
    obtain ⟨hnW, hgt⟩ := hn
    by_cases hnN : n ≤ N
    · by_cases hb : Int.fract (F γ n) ≤ 1 - 1 / 4 * Δ
      · exact Or.inl ⟨hnW, hnN, hgt, hb⟩
      · exact Or.inr (Or.inl ⟨hnW, hnN, lt_of_not_ge hb⟩)
    · have hnN' : N < n := Nat.lt_of_not_le hnN
      by_cases hb : Int.fract (F γ n) ≤ 1 - 1 / 4 * Δ
      · exact Or.inr (Or.inr (Or.inl ⟨hnW, hnN', hgt, hb⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hnW, hnN', lt_of_not_ge hb⟩))
  have hcard : A.card ≤ L1.card + (M1.card + (L2.card + M2.card)) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le L1 (M1 ∪ (L2 ∪ M2))
    have h3 := Finset.card_union_le M1 (L2 ∪ M2)
    have h4 := Finset.card_union_le L2 M2
    omega
  have hA1 : (L1.card : ℝ) ≤ B1 * N * Δ := hN1 N hN1'
  have hA2 : (M1.card : ℝ) ≤ B2 * N * Δ := hN2 N hN2'
  have hA3 : (L2.card : ℝ) ≤ B3 * N * Δ := hN3 N hN3'
  have hA4 : (M2.card : ℝ) ≤ B4 * N * Δ := hN4 N hN4'
  have hsum : (A.card : ℝ) ≤
      (L1.card : ℝ) + (M1.card : ℝ) + (L2.card : ℝ) + (M2.card : ℝ) := by
    have := hcard
    have hcast : (A.card : ℝ) ≤ ((L1.card + (M1.card + (L2.card + M2.card)) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hcast
    linarith
  have hgoal : (A.card : ℝ) ≤ (B1 + B2 + B3 + B4) * N * Δ := by
    calc (A.card : ℝ) ≤ (L1.card : ℝ) + (M1.card : ℝ) + (L2.card : ℝ) + (M2.card : ℝ) := hsum
      _ ≤ B1 * N * Δ + B2 * N * Δ + B3 * N * Δ + B4 * N * Δ := by linarith
      _ = (B1 + B2 + B3 + B4) * N * Δ := by ring
  exact hgoal

end LeanLab.ExceptionalSet.Decomp371a

#print axioms LeanLab.ExceptionalSet.Decomp371a.leaf_boundary_outer_high_split
