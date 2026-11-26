/-
Jia 1996 pages 270 to 273, Lemma 24: split of the group 1 remainder transfer
into the 25 source cells of the explicit integrals and their disjointness.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The cell transfers remain OPEN LEAF inputs; the cell disjointness is proved;
the assembly below is proved from them.
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

/-- Pages 271 to 273 support: two affine inner intervals over the outer range
Y^a < p ≤ Y^b are separated when the slope gap is controlled at the matching end.
This is the comparison of p^e Y^f with p^c' Y^d' used for the cells of Lemma 24. -/
theorem key_sep (Y p q a b e f c' d' : ℝ) (hY : 1 < Y) (hp : 0 < p)
    (h1 : Y ^ a < p) (h2 : p ≤ Y ^ b) (hq1 : q ≤ p ^ e * Y ^ f) (hq2 : p ^ c' * Y ^ d' < q)
    (hsep : (0 ≤ e - c' ∧ b * (e - c') ≤ d' - f) ∨ (e - c' ≤ 0 ∧ a * (e - c') ≤ d' - f)) :
    False := by
  have hY0 : 0 < Y := by linarith
  have hk : p ^ (e - c') ≤ Y ^ (d' - f) := by
    rcases hsep with ⟨hk0, hkm⟩ | ⟨hk0, hkm⟩
    · calc p ^ (e - c') ≤ (Y ^ b) ^ (e - c') := rpow_le_rpow hp.le h2 hk0
        _ = Y ^ (b * (e - c')) := (rpow_mul hY0.le _ _).symm
        _ ≤ Y ^ (d' - f) := rpow_le_rpow_of_exponent_le hY.le hkm
    · calc p ^ (e - c') ≤ (Y ^ a) ^ (e - c') :=
            rpow_le_rpow_of_nonpos (rpow_pos_of_pos hY0 _) h1.le hk0
        _ = Y ^ (a * (e - c')) := (rpow_mul hY0.le _ _).symm
        _ ≤ Y ^ (d' - f) := rpow_le_rpow_of_exponent_le hY.le hkm
  have he : p ^ e = p ^ c' * p ^ (e - c') := by
    rw [← rpow_add hp]; congr 1; ring
  have hd : Y ^ d' = Y ^ f * Y ^ (d' - f) := by
    rw [← rpow_add hY0]; congr 1; ring
  have hpc : 0 < p ^ c' := rpow_pos_of_pos hp _
  have hYf : 0 < Y ^ f := rpow_pos_of_pos hY0 _
  have : p ^ e * Y ^ f ≤ p ^ c' * Y ^ d' := by
    rw [he, hd]
    have := mul_le_mul_of_nonneg_left hk (mul_pos hpc hYf).le
    nlinarith
  linarith

/-- Pages 271 to 273 support: the rational separation test for two rows of `data`,
either separated outer ranges or separated affine inner ranges. -/
def sepQ (i j : Fin 25) : Prop :=
  data i 1 ≤ data j 0 ∨ data j 1 ≤ data i 0 ∨
  ((0 ≤ data i 4 - data j 2 ∧ data i 1 * (data i 4 - data j 2) ≤ data j 3 - data i 5) ∨
    (data i 4 - data j 2 ≤ 0 ∧ data i 0 * (data i 4 - data j 2) ≤ data j 3 - data i 5)) ∨
  ((0 ≤ data j 4 - data i 2 ∧ data j 1 * (data j 4 - data i 2) ≤ data i 3 - data j 5) ∨
    (data j 4 - data i 2 ≤ 0 ∧ data j 0 * (data j 4 - data i 2) ≤ data i 3 - data j 5))

instance : DecidableRel sepQ := fun i j => by unfold sepQ; infer_instance

/-- Pages 271 to 273: any two distinct printed rows pass the separation test. -/
theorem sepQ_all : ∀ i j : Fin 25, i ≠ j → sepQ i j := by decide +kernel

/-- Pages 271 to 273: a prime pair lies in at most one of the 25 cells. -/
theorem cell_unique (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (i j : Fin 25)
    (hi : Y ^ (data i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (data i 1 : ℝ) ∧
      (p : ℝ) ^ (data i 2 : ℝ) * Y ^ (data i 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) ≤ (p : ℝ) ^ (data i 4 : ℝ) * Y ^ (data i 5 : ℝ))
    (hj : Y ^ (data j 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (data j 1 : ℝ) ∧
      (p : ℝ) ^ (data j 2 : ℝ) * Y ^ (data j 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) ≤ (p : ℝ) ^ (data j 4 : ℝ) * Y ^ (data j 5 : ℝ)) : i = j := by
  by_contra hne
  have hs := sepQ_all i j hne
  unfold sepQ at hs
  obtain ⟨hi0, hi1, hi2, hi3⟩ := hi
  obtain ⟨hj0, hj1, hj2, hj3⟩ := hj
  have hp0 : (0 : ℝ) < p := lt_trans (rpow_pos_of_pos (by linarith) _) hi0
  rcases hs with hs | hs | hs | hs
  · have h : ((data i 1 : ℚ) : ℝ) ≤ ((data j 0 : ℚ) : ℝ) := by exact_mod_cast hs
    have := rpow_le_rpow_of_exponent_le hY.le h
    linarith
  · have h : ((data j 1 : ℚ) : ℝ) ≤ ((data i 0 : ℚ) : ℝ) := by exact_mod_cast hs
    have := rpow_le_rpow_of_exponent_le hY.le h
    linarith
  · exact key_sep Y p q _ _ _ _ _ _ hY hp0 hi0 hi1 hi3 hj2 (by exact_mod_cast hs)
  · exact key_sep Y p q _ _ _ _ _ _ hY hp0 hj0 hj1 hj3 hi2 (by exact_mod_cast hs)

/-- PROVED, formerly LEAF MEDIUM: Jia pages 271 to 273, the 25 integration cells of Lemma 24 are pairwise disjoint,
so the remainder sum dominates the sum of the cell sums. MEDIUM.
Rows sharing an outer interval have adjacent or separated affine inner intervals;
rows with different outer intervals are separated by the half open outer condition.
A rational check over the printed rows found no overlap. -/
theorem cells_le_remainder (N Y : ℝ) (n : ℕ) (hY : 1 < Y) :
    ∑ i : Fin 25, cellSum i N Y n ≤ pieceSum 1 11 false N Y n := by
  have hcell : ∀ i : Fin 25, cellSum i N Y n = ∑ p ∈ range (n + 1), ∑ q ∈ range (n + 1),
      if ((p.Prime ∧ Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)) ∧ (q.Prime ∧ Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))))) ∧ (Y ^ (data i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (data i 1 : ℝ) ∧ (p : ℝ) ^ (data i 2 : ℝ) * Y ^ (data i 3 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (p : ℝ) ^ (data i 4 : ℝ) * Y ^ (data i 5 : ℝ)) then (if groupOf (regionIndex Y p q) = 1 ∧ decide (regionIndex Y p q = 11) = false then (sifted N Y n (p * q) q : ℝ) else 0) else 0 := by
    intro i
    unfold cellSum
    rw [sum_filter]
    refine sum_congr rfl (fun p _ => ?_)
    split_ifs with hp
    · rw [sum_filter]
      refine sum_congr rfl (fun q _ => ?_)
      exact if_congr (by tauto) rfl rfl
    · symm
      apply sum_eq_zero
      intro q _
      exact if_neg (by tauto)
  have hpiece : pieceSum 1 11 false N Y n = ∑ p ∈ range (n + 1), ∑ q ∈ range (n + 1),
      if (p.Prime ∧ Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)) ∧ (q.Prime ∧ Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))) then (if groupOf (regionIndex Y p q) = 1 ∧ decide (regionIndex Y p q = 11) = false then (sifted N Y n (p * q) q : ℝ) else 0) else 0 := by
    unfold pieceSum
    rw [sum_filter]
    refine sum_congr rfl (fun p _ => ?_)
    split_ifs with hp
    · rw [sum_filter]
      refine sum_congr rfl (fun q _ => ?_)
      exact if_congr (by tauto) rfl rfl
    · symm
      apply sum_eq_zero
      intro q _
      exact if_neg (by tauto)
  rw [hpiece, sum_congr rfl (fun i _ => hcell i), sum_comm]
  apply sum_le_sum
  intro p _
  rw [sum_comm]
  apply sum_le_sum
  intro q _
  have hg0 : (0 : ℝ) ≤ (if groupOf (regionIndex Y p q) = 1 ∧ decide (regionIndex Y p q = 11) = false then (sifted N Y n (p * q) q : ℝ) else 0) := by split_ifs <;> positivity
  by_cases hb : (p.Prime ∧ Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)) ∧ (q.Prime ∧ Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))))
  · rw [if_pos hb]
    by_cases hex : ∃ i : Fin 25, (Y ^ (data i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (data i 1 : ℝ) ∧ (p : ℝ) ^ (data i 2 : ℝ) * Y ^ (data i 3 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (p : ℝ) ^ (data i 4 : ℝ) * Y ^ (data i 5 : ℝ))
    · obtain ⟨i0, hi0⟩ := hex
      have hrw : ∀ i : Fin 25, (if ((p.Prime ∧ Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)) ∧ (q.Prime ∧ Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))))) ∧ (Y ^ (data i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (data i 1 : ℝ) ∧ (p : ℝ) ^ (data i 2 : ℝ) * Y ^ (data i 3 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (p : ℝ) ^ (data i 4 : ℝ) * Y ^ (data i 5 : ℝ)) then (if groupOf (regionIndex Y p q) = 1 ∧ decide (regionIndex Y p q = 11) = false then (sifted N Y n (p * q) q : ℝ) else 0) else 0) =
          if i = i0 then (if groupOf (regionIndex Y p q) = 1 ∧ decide (regionIndex Y p q = 11) = false then (sifted N Y n (p * q) q : ℝ) else 0) else 0 := by
        intro i
        by_cases hi : i = i0
        · subst hi
          rw [if_pos ⟨hb, hi0⟩, if_pos rfl]
        · rw [if_neg hi, if_neg]
          rintro ⟨_, hc⟩
          exact hi (cell_unique Y hY p q i i0 hc hi0)
      rw [sum_congr rfl (fun i _ => hrw i), sum_ite_eq' univ i0]
      simp
    · rw [sum_eq_zero (fun i _ => if_neg (fun h => hex ⟨i, h.2⟩))]
      exact hg0
  · rw [if_neg hb]
    apply le_of_eq
    apply sum_eq_zero
    intro i _
    exact if_neg (fun h => hb h.1)

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
