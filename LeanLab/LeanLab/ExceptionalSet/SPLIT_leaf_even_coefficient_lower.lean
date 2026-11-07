import LeanLab.ExceptionalSet.Decomp446a

/-!
Split of the even major arc coefficient estimate `leaf_even_coefficient_lower` of Decomp446a.

The statement to be split says: for `1 < γ < 3/2` there are a positive cap `δ₀`, a positive cap
`κ₀`, a positive threshold constant `c₀`, a positive `B` and an `N₀` such that for every admissible
`δ`, every positive `κ` below the cap and every `N ≥ N₀`, the number of indices `n` in the floor
window whose even adjacent major arc coefficient has real part below `c₀ F(γ,N) ℰ^(-1/10)` is at
most `B N ℰ^(-1/12)`.

The split follows the parity of `ν_n = ⌊F(γ,n)⌋`. That parity is exactly what decides which of the
two adjacent integers is the even one: for even `ν_n` the even adjacent integer is `ν_n` itself, and
for odd `ν_n` it is `ν_n + 1`. The estimate is therefore asked for on each of the two halves of the
window separately, each over strictly fewer indices than the whole window and each for its own
adjacent integer. The assembly splits the window by that parity, adds the two counts and merges the
two constants into one positive `B`. Both pieces are strictly weaker than the whole estimate: each
counts a subset of the same window, and neither fixes the other adjacent integer.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.Adjacent446 (evenAdjacent)

/-- LEAF. Even index piece: the same eventual counting bound as the whole estimate, restricted to
the indices of the window whose floor value `ν_n` is even. On those indices the even adjacent
integer is `ν_n` itself, so this is the estimate for one of the two adjacent integers and only over
a subset of the window indices. -/
theorem leaf_even_coefficient_lower_even_index (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- LEAF. Odd index piece: the same eventual counting bound as the whole estimate, restricted to
the indices of the window whose floor value `ν_n` is odd. On those indices the even adjacent
integer is the upper neighbour `ν_n + 1`, so this is the estimate for the other adjacent integer
and only over a subset of the window indices. -/
theorem leaf_even_coefficient_lower_odd_index (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- Assembly. The even adjacent coefficient count over the floor window follows from the two parity
pieces: the even adjacent integer of an index with even `ν_n` is `ν_n`, and of an index with odd
`ν_n` is `ν_n + 1`, so the counted set is the union of the two parity pieces; their counts add; the
two caps are minimised, the two constants are added, and the smaller of the two thresholds replaces
both since the window factor is nonnegative. Every step of the assembly is proved. -/
theorem leaf_even_coefficient_lower_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δe, hδe, he⟩ := leaf_even_coefficient_lower_even_index γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := leaf_even_coefficient_lower_odd_index γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κe κo, lt_min hκe hκo, fun κ hκ hκsmall => ?_⟩
  obtain ⟨ce, Be, hce, hBe, Ne, he⟩ := he κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨co, Bo, hco, hBo, No, ho⟩ := ho κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨min ce co, Be + Bo, lt_min hce hco, add_pos hBe hBo, max Ne No, fun N hN => ?_⟩
  have hNe : Ne ≤ N := (le_max_left _ _).trans hN
  have hNo : No ≤ N := (le_max_right _ _).trans hN
  have hF : 0 ≤ F γ N := (Real.exp_pos _).le
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hR : 0 ≤ calE γ κ N ^ (-(1 / 10 : ℝ)) := (Real.rpow_pos_of_pos hE _).le
  have hstepE : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hF) hR
  have hstepO : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hF) hR
  have hA : ((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      Be * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    have hsub : (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card ≤
        (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
            ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hwin, hlt⟩ := Finset.mem_filter.mp hn
      have hpar : Even (nu γ n) := (Finset.mem_filter.mp hwin).2
      have hadj : evenAdjacent γ n = nu γ n := by simp [evenAdjacent, hpar]
      rw [hadj] at hlt
      exact Finset.mem_filter.mpr ⟨hwin, lt_of_lt_of_le hlt hstepE⟩
    exact (Nat.cast_le.mpr hsub).trans (he N hNe)
  have hB : ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      Bo * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    have hsub : (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card ≤
        (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
            co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hwin, hlt⟩ := Finset.mem_filter.mp hn
      have hpar : ¬ Even (nu γ n) := (Finset.mem_filter.mp hwin).2
      have hadj : evenAdjacent γ n = nu γ n + 1 := by simp [evenAdjacent, hpar]
      rw [hadj] at hlt
      exact Finset.mem_filter.mpr ⟨hwin, lt_of_lt_of_le hlt hstepO⟩
    exact (Nat.cast_le.mpr hsub).trans (ho N hNo)
  have hpart : (window γ N).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) =
      (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) ∪
      (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hnw, hb⟩
      by_cases hpar : Even (nu γ n)
      · exact Or.inl ⟨⟨hnw, hpar⟩, hb⟩
      · exact Or.inr ⟨⟨hnw, hpar⟩, hb⟩
    · rintro (⟨⟨hnw, _⟩, hb⟩ | ⟨⟨hnw, _⟩, hb⟩)
      · exact ⟨hnw, hb⟩
      · exact ⟨hnw, hb⟩
  have hdisj : Disjoint
      (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))))
      (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).2
  rw [hpart, Finset.card_union_of_disjoint hdisj]
  push_cast
  refine (add_le_add hA hB).trans_eq ?_
  ring

end LeanLab.ExceptionalSet.Decomp446a
