/-
Jia 1996 pages 263 and 277 to 279, displays 48 and 53 to 56: split of
`Decomp568a.region4_transfer_exception` into the region bookkeeping of display 52
and the lower and upper halves of the prime to integer model transfer.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The three LEAF inputs remain OPEN; the assembly below is proved from them.
-/
import LeanLab.Languasco2004.Decomp568a

namespace LeanLab.Languasco2004.Feed568aTransfer4
open Finset Real Decomp279a Decomp316a Decomp316c GroupSplit548 Decomp568a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 279 and page 263 display 48: the sifted prime counts S of A_pq and q over the
full Omega4 domain Y^(41/180) < p ≤ Y^(8/33) and Y^(41/90) / p < q < p,
with the same index sets as the integer model `model4`. -/
def omega4Sum (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
      Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
    ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
      (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
      (sifted N Y n (p * q) q : ℝ)

/-- LEAF: Jia pages 267 to 269 display 52 and page 279, the selected Omega4 piece is the
sum over the full Omega4 domain. MEDIUM.
Regions 1 to 3 of the least label convention do not meet region 4, label 4 lies in group 3,
and for large N every recovery cap and the range caps n + 1 and 2 Y + 1 are inactive
on the Omega4 domain, since Y ^ (41/90) / p exceeds Y ^ (16/135) and p cubed is below 2 Y. -/
theorem region4_piece_eq :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 12 → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ n ∈ window N ε,
      pieceSum 3 4 true N (localization N ε) n = omega4Sum N (localization N ε) n := by
  sorry

/-- LEAF: Jia pages 277 to 279, displays 53 to 56, lower half of the prime to integer
model transfer, using Lemmas 13, 17, 18 and 19 and the Iwaniec sieve, with the exception
convention before display 48 on page 263. HARD. -/
theorem omega4_transfer_lower :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        omega4Sum N (localization N ε) n <
          singular n / Real.log N * model4 (localization N ε) -
            η * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  sorry

/-- LEAF: Jia pages 277 to 279, displays 53 to 56, upper half of the prime to integer
model transfer, by the same Lemmas 13, 17, 18 and 19 and the Iwaniec sieve,
with the exception convention before display 48 on page 263. HARD. -/
theorem omega4_transfer_upper :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        singular n / Real.log N * model4 (localization N ε) +
            η * scale N (localization N ε) n <
          omega4Sum N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  sorry

/-- Jia pages 277 to 279: the exact statement of `Decomp568a.region4_transfer_exception`,
proved from the LEAF inputs `region4_piece_eq`, `omega4_transfer_lower` and
`omega4_transfer_upper`. -/
theorem region4_transfer_exception_from_leaves :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        η * scale N (localization N ε) n <
        |pieceSum 3 4 true N (localization N ε) n -
          singular n / Real.log N * model4 (localization N ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  intro η hη
  obtain ⟨e1, he1, hL⟩ := omega4_transfer_lower η hη
  obtain ⟨e2, he2, hU⟩ := omega4_transfer_upper η hη
  refine ⟨min e1 (min e2 (1 / 12)), lt_min he1 (lt_min he2 (by norm_num)), ?_⟩
  intro ε B hε he hB
  have hε1 : ε < e1 := he.trans_le (min_le_left _ _)
  have hε2 : ε < e2 := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε < 1 / 12 := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C1, N1, hC1⟩ := hL ε B hε hε1 hB
  obtain ⟨C2, N2, hC2⟩ := hU ε B hε hε2 hB
  obtain ⟨N3, hN3⟩ := region4_piece_eq ε hε hε3
  refine ⟨C1 + C2, max N1 (max N2 N3), ?_⟩
  intro N hN
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2 : N2 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN3' : N3 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  set Y := localization N ε with hYdef
  have hsub : (window N ε).filter (fun n =>
        η * scale N Y n < |pieceSum 3 4 true N Y n - singular n / Real.log N * model4 Y|) ⊆
      (window N ε).filter (fun n =>
        omega4Sum N Y n < singular n / Real.log N * model4 Y - η * scale N Y n) ∪
      (window N ε).filter (fun n =>
        singular n / Real.log N * model4 Y + η * scale N Y n < omega4Sum N Y n) := by
    intro n hn
    obtain ⟨hnw, hbad⟩ := mem_filter.mp hn
    rw [hN3 N hN3' n hnw] at hbad
    rw [mem_union, mem_filter, mem_filter]
    rcases lt_abs.mp hbad with h | h
    · right
      exact ⟨hnw, by linarith⟩
    · left
      exact ⟨hnw, by linarith⟩
  calc (((window N ε).filter (fun n =>
        η * scale N Y n <
          |pieceSum 3 4 true N Y n - singular n / Real.log N * model4 Y|)).card : ℝ)
      ≤ (((window N ε).filter (fun n =>
          omega4Sum N Y n < singular n / Real.log N * model4 Y - η * scale N Y n) ∪
        (window N ε).filter (fun n =>
          singular n / Real.log N * model4 Y + η * scale N Y n <
            omega4Sum N Y n)).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ (((window N ε).filter (fun n =>
          omega4Sum N Y n < singular n / Real.log N * model4 Y -
            η * scale N Y n)).card : ℝ) +
        (((window N ε).filter (fun n =>
          singular n / Real.log N * model4 Y + η * scale N Y n <
            omega4Sum N Y n)).card : ℝ) := by
        exact_mod_cast card_union_le _ _
    _ ≤ C1 * windowLength N ε / Real.log N ^ B + C2 * windowLength N ε / Real.log N ^ B :=
        add_le_add (hC1 N hN1) (hC2 N hN2)
    _ = (C1 + C2) * windowLength N ε / Real.log N ^ B := by ring

#print axioms region4_piece_eq
#print axioms omega4_transfer_lower
#print axioms omega4_transfer_upper
#print axioms region4_transfer_exception_from_leaves
end
end LeanLab.Languasco2004.Feed568aTransfer4
