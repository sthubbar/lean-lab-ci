/-
Jia 1996 pages 270 to 273, Lemma 24: split of the group 1 remainder transfer
into the 25 source cells of the explicit integrals and their disjointness.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The cell transfers remain OPEN LEAF inputs; the assembly below is proved from them.
-/
import LeanLab.Languasco2004.Decomp566c

namespace LeanLab.Languasco2004.Feed566cRemainder
open Finset Real Decomp279a Decomp316c GroupSplit548 RemainderData566 Decomp566b Decomp566c
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 271 to 273: the prime pairs of source cell i of Lemma 24.
The outer prime is Y^a < p ≤ Y^b and the inner prime is
p^c Y^d < q ≤ p^e Y^f, with the row a, b, c, d, e, f of `data i`,
which is the affine inner domain of `term i` after t = log p / log Y and
u = log q / log Y. The recovery caps and the remainder selection of
`pieceSum 1 11 false` are kept, so a cell only counts remainder pairs. -/
def cellSum (i : Fin 25) (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
    Y ^ (data i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (data i 1 : ℝ)),
    ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) ∧
      (p : ℝ) ^ (data i 2 : ℝ) * Y ^ (data i 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) ≤ (p : ℝ) ^ (data i 4 : ℝ) * Y ^ (data i 5 : ℝ)),
      if groupOf (regionIndex Y p q) = 1 ∧ decide (regionIndex Y p q = 11) = false
        then (sifted N Y n (p * q) q : ℝ) else 0

/-- LEAF: Jia pages 271 to 273, the 25 integration cells of Lemma 24 are pairwise disjoint,
so the remainder sum dominates the sum of the cell sums. MEDIUM.
Rows sharing an outer interval have adjacent or separated affine inner intervals;
rows with different outer intervals are separated by the half open outer condition.
A rational check over the printed rows found no overlap. -/
theorem cells_le_remainder (N Y : ℝ) (n : ℕ) (hY : 1 < Y) :
    ∑ i : Fin 25, cellSum i N Y n ≤ pieceSum 1 11 false N Y n := by
  sorry

/-- LEAF: Jia pages 270 to 273, Lemma 24, the prime transfer for one source cell. HARD.
Following the Omega11 argument with the applicable mean value regions,
Lemmas 18 and 21 and the Lemma 20 lower kernel 0.5607, the sifted prime count of cell i
is at least its explicit double integral term i times the main term,
outside an exceptional set with the logarithmic saving of page 263. -/
theorem cell_transfer (i : Fin 25) :
    ∀ η : ℝ, 0 < η →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        cellSum i N (localization N ε) n <
          (term i - η) * scale N (localization N ε) n)).card : ℝ) ≤
        C * windowLength N ε / Real.log N ^ B := by
  sorry

/-- Pages 270 to 273: the strict failure count of the remainder transfer,
assembled from the 25 cell transfers and the disjointness of the cells. -/
theorem remainder_count_from_leaves (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        pieceSum 1 11 false N (localization N ε) n +
          η * scale N (localization N ε) n <
            model * scale N (localization N ε) n)).card : ℝ) ≤
        C * windowLength N ε / Real.log N ^ B := by
  have hη' : 0 < η / 25 := by positivity
  choose e he hcell using fun i : Fin 25 => cell_transfer i (η / 25) hη'
  let ε₀ : ℝ := univ.inf' univ_nonempty e
  have hε₀ : 0 < ε₀ := (lt_inf'_iff univ_nonempty).mpr (fun i _ => he i)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε B hε hεε₀ hB
  have hεi : ∀ i, ε < e i := fun i =>
    hεε₀.trans_le (inf'_le e (mem_univ i))
  choose C N₀ hC using fun i : Fin 25 => hcell i ε B hε (hεi i) hB
  refine ⟨∑ i : Fin 25, C i, max 2 (univ.sup' univ_nonempty N₀), ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNi : ∀ i, N₀ i ≤ N := fun i =>
    (le_sup' N₀ (mem_univ i)).trans ((le_max_right _ _).trans hN)
  have hY : 1 < localization N ε := by
    unfold localization
    exact Real.one_lt_rpow (by linarith) (by linarith)
  set Y := localization N ε with hYdef
  have hsub : (window N ε).filter (fun n =>
      pieceSum 1 11 false N Y n + η * scale N Y n < model * scale N Y n) ⊆
      univ.biUnion (fun i : Fin 25 => (window N ε).filter (fun n =>
        cellSum i N Y n < (term i - η / 25) * scale N Y n)) := by
    intro n hn
    obtain ⟨hnw, hbad⟩ := mem_filter.mp hn
    rw [mem_biUnion]
    by_contra hnot
    push Not at hnot
    have hgood : ∀ i : Fin 25, (term i - η / 25) * scale N Y n ≤ cellSum i N Y n := by
      intro i
      have := hnot i (mem_univ i)
      rw [mem_filter, not_and, not_lt] at this
      exact this hnw
    have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 25))) => hgood i)
    have hmodel : ∑ i : Fin 25, (term i - η / 25) * scale N Y n =
        model * scale N Y n - η * scale N Y n := by
      rw [← sum_mul, sum_sub_distrib]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold model
      ring
    have hcells := cells_le_remainder N Y n hY
    linarith
  calc (((window N ε).filter (fun n =>
        pieceSum 1 11 false N Y n + η * scale N Y n < model * scale N Y n)).card : ℝ)
      ≤ ((univ.biUnion (fun i : Fin 25 => (window N ε).filter (fun n =>
          cellSum i N Y n < (term i - η / 25) * scale N Y n))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ i : Fin 25, (((window N ε).filter (fun n =>
          cellSum i N Y n < (term i - η / 25) * scale N Y n)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ i : Fin 25, C i * windowLength N ε / Real.log N ^ B :=
        sum_le_sum (fun i _ => hC i N (hNi i))
    _ = (∑ i : Fin 25, C i) * windowLength N ε / Real.log N ^ B := by
        rw [sum_mul, sum_div]

/-- Jia pages 270 to 273, Lemma 24: the exact statement of
`Decomp566c.remainder_transfer`, proved from the LEAF inputs
`cells_le_remainder` and `cell_transfer` of this file. -/
theorem remainder_transfer_from_leaves :
    ∀ η : ℝ, 0 < η →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∃ E : Finset ℕ,
      (E.card : ℝ) ≤ C * windowLength N ε / Real.log N ^ B ∧
      ∀ n ∈ window N ε, n ∉ E →
        model * scale N (localization N ε) n ≤
          pieceSum 1 11 false N (localization N ε) n + η * scale N (localization N ε) n := by
  intro η hη
  obtain ⟨ε₀, hε₀, h⟩ := remainder_count_from_leaves η hη
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε B hε hεε₀ hB
  obtain ⟨C, N₀, hC⟩ := h ε B hε hεε₀ hB
  exact ⟨C, N₀, fun N hN =>
    (remainder_exception_iff N ε η
      (C * windowLength N ε / Real.log N ^ B)).mpr (hC N hN)⟩

#print axioms cells_le_remainder
#print axioms cell_transfer
#print axioms remainder_count_from_leaves
#print axioms remainder_transfer_from_leaves
end
end LeanLab.Languasco2004.Feed566cRemainder
