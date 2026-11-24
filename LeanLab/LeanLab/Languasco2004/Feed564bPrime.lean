/-
Jia 1996 Lemma 27, pages 280 to 282, with Lemma 11 on pages 231 to 233,
Lemma 18 display 32 on page 253 and its page 260 exceptional set argument.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Split of Decomp564b.prime_to_rough11 into cited LEAF steps, burst-20261122.
The parent statement is proved below from the leaves, CONDITIONAL ON the open leaves.
-/
import LeanLab.Languasco2004.Model564

namespace LeanLab.Languasco2004.Feed564bPrime
open Finset Real Decomp279a Decomp316c Model564
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Jia page 280: the prime sum S of A_pq and q over a finite family of source regions,
indexed by the same unclipped finite set of prime pairs as the arithmetic B model roughModel. -/
def pairModel (labels : Finset ℕ) (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
    if p.Prime ∧ q.Prime ∧ regionIndex Y p q ∈ labels then (sifted N Y n (p * q) q : ℝ) else 0

/-- Page 280: disjoint source region families have additive prime sums. -/
theorem pairModel_union (s t : Finset ℕ) (h : Disjoint s t) (N Y : ℝ) (n : ℕ) :
    pairModel (s ∪ t) N Y n = pairModel s N Y n + pairModel t N Y n := by
  unfold pairModel
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have hn : ¬ (regionIndex Y p q ∈ s ∧ regionIndex Y p q ∈ t) :=
    fun hh => (disjoint_left.mp h) hh.1 hh.2
  by_cases hs : regionIndex Y p q ∈ s <;>
    by_cases ht : regionIndex Y p q ∈ t <;>
    by_cases hp' : p.Prime <;> by_cases hq' : q.Prime <;> simp_all

/-- Page 280: the transfer for a union of two disjoint region families follows from the
transfers for each family, splitting the reserve delta in two halves. -/
theorem transfer_union (s t : Finset ℕ) (hst : Disjoint s t)
    (hs : ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n =>
          pairModel s N (localization N ε) n + δ * scale N (localization N ε) n <
            singular n / Real.log N * roughModel s (localization N ε))).card : ℝ) ≤
        C * windowLength N ε / Real.log N ^ B)
    (ht : ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n =>
          pairModel t N (localization N ε) n + δ * scale N (localization N ε) n <
            singular n / Real.log N * roughModel t (localization N ε))).card : ℝ) ≤
        C * windowLength N ε / Real.log N ^ B) :
    ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n =>
          pairModel (s ∪ t) N (localization N ε) n + δ * scale N (localization N ε) n <
            singular n / Real.log N * roughModel (s ∪ t) (localization N ε))).card : ℝ) ≤
        C * windowLength N ε / Real.log N ^ B := by
  intro δ hδ
  obtain ⟨e1, he1, h1⟩ := hs (δ / 2) (by linarith)
  obtain ⟨e2, he2, h2⟩ := ht (δ / 2) (by linarith)
  refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
  intro ε B hε he hB
  obtain ⟨C1, N1, hC1⟩ := h1 ε B hε (he.trans_le (min_le_left _ _)) hB
  obtain ⟨C2, N2, hC2⟩ := h2 ε B hε (he.trans_le (min_le_right _ _)) hB
  refine ⟨C1 + C2, max N1 N2, ?_⟩
  intro N hN
  set Y := localization N ε
  have hsub : (window N ε).filter (fun n =>
      pairModel (s ∪ t) N Y n + δ * scale N Y n <
        singular n / Real.log N * roughModel (s ∪ t) Y) ⊆
      (window N ε).filter (fun n => pairModel s N Y n + δ / 2 * scale N Y n <
        singular n / Real.log N * roughModel s Y) ∪
      (window N ε).filter (fun n => pairModel t N Y n + δ / 2 * scale N Y n <
        singular n / Real.log N * roughModel t Y) := by
    intro n hn
    obtain ⟨hw, hlt⟩ := mem_filter.mp hn
    rw [pairModel_union s t hst, roughModel_union s t hst] at hlt
    rw [mem_union, mem_filter, mem_filter]
    by_contra hc
    push_neg at hc
    have a := hc.1 hw
    have b := hc.2 hw
    nlinarith
  have hc : (((window N ε).filter (fun n =>
      pairModel (s ∪ t) N Y n + δ * scale N Y n <
        singular n / Real.log N * roughModel (s ∪ t) Y)).card : ℝ) ≤
      (((window N ε).filter (fun n => pairModel s N Y n + δ / 2 * scale N Y n <
        singular n / Real.log N * roughModel s Y)).card : ℝ) +
      (((window N ε).filter (fun n => pairModel t N Y n + δ / 2 * scale N Y n <
        singular n / Real.log N * roughModel t Y)).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have := add_le_add (hC1 N ((le_max_left _ _).trans hN)) (hC2 N ((le_max_right _ _).trans hN))
  calc _ ≤ _ := hc
    _ ≤ _ := this
    _ = _ := by ring

/-- Page 280: generic assembly over a nonempty finite family of source regions.
The transfer for the family follows from the transfer for each single region. -/
theorem transfer_of_regions (labels : Finset ℕ) (hne : labels.Nonempty)
    (hreg : ∀ i ∈ labels, ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n =>
          pairModel {i} N (localization N ε) n + δ * scale N (localization N ε) n <
            singular n / Real.log N * roughModel {i} (localization N ε))).card : ℝ) ≤
        C * windowLength N ε / Real.log N ^ B) :
    ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n =>
          pairModel labels N (localization N ε) n + δ * scale N (localization N ε) n <
            singular n / Real.log N * roughModel labels (localization N ε))).card : ℝ) ≤
        C * windowLength N ε / Real.log N ^ B := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a => exact hreg a (mem_singleton_self a)
  | cons a s ha hs ih =>
    have hd : Disjoint {a} s := disjoint_singleton_left.mpr ha
    have he : s.cons a ha = {a} ∪ s := by rw [cons_eq_insert, insert_eq]
    rw [he]
    exact transfer_union {a} s hd (hreg a (by simp))
      (ih fun i hi => hreg i (by simp [hi]))

/-- Page 280: the prime model exceeds the unclipped prime sum once the clipping holds. -/
theorem prime_transfer_of_pair (labels : Finset ℕ)
    (hclip : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ n ∈ window N ε,
        pairModel labels N (localization N ε) n ≤ primeModel labels N (localization N ε) n)
    (hpair : ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n =>
          pairModel labels N (localization N ε) n + δ * scale N (localization N ε) n <
            singular n / Real.log N * roughModel labels (localization N ε))).card : ℝ) ≤
        C * windowLength N ε / Real.log N ^ B)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        primeModel labels N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel labels (localization N ε))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e1, he1, h1⟩ := hclip
  obtain ⟨e2, he2, h2⟩ := hpair δ hδ
  refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
  intro ε B hε he hB
  obtain ⟨M, hM⟩ := h1 ε hε (he.trans_le (min_le_left _ _))
  obtain ⟨C, N2, hC⟩ := h2 ε B hε (he.trans_le (min_le_right _ _)) hB
  refine ⟨C, max M N2, ?_⟩
  intro N hN
  have hsub : (window N ε).filter (fun n =>
      primeModel labels N (localization N ε) n + δ * scale N (localization N ε) n <
        singular n / Real.log N * roughModel labels (localization N ε)) ⊆
      (window N ε).filter (fun n =>
        pairModel labels N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel labels (localization N ε)) := by
    intro n hn
    obtain ⟨hw, hlt⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hw, by linarith [hM N ((le_max_left _ _).trans hN) n hw]⟩
  have hc : (((window N ε).filter (fun n =>
      primeModel labels N (localization N ε) n + δ * scale N (localization N ε) n <
        singular n / Real.log N * roughModel labels (localization N ε))).card : ℝ) ≤
      (((window N ε).filter (fun n =>
        pairModel labels N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel labels (localization N ε))).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hc.trans (hC N ((le_max_right _ _).trans hN))

/-- LEAF: Jia page 280 clipping, for n in the basic interval every prime pair of regions 33,
36, 38, 40, 42, 46 and 49 satisfies Y^(16/135) < q < min p (sqrt (2Y/p)) and p ≤ sqrt (2Y),
so the unclipped prime sum is a subsum of the clipped prime model. MEDIUM -/
theorem pairModel11_le_primeModel :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ n ∈ window N ε,
        pairModel labels11 N (localization N ε) n ≤ primeModel labels11 N (localization N ε) n := by
  sorry

/-- LEAF: Jia Lemma 11 pages 231 to 233 with Lemma 18 display 32 on page 253 and the page 260
exceptional set argument, applied to one source region D_i, i in 33, 36, 38, 40, 42, 46, 49:
outside an exceptional set the prime sum S of A_pq and q over D_i is at least the singular
factor over log N times the arithmetic B model of D_i, minus delta times the main term. HARD -/
theorem region_transfer11 (i : ℕ) (hi : i ∈ labels11) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        pairModel {i} N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel {i} (localization N ε))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia Lemma 27 pages 280 and 281: Decomp564b.prime_to_rough11 from the leaves.
CONDITIONAL ON pairModel11_le_primeModel and region_transfer11. Same type as the parent. -/
theorem prime_to_rough11_from_leaves (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        primeModel labels11 N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel labels11 (localization N ε))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B :=
  prime_transfer_of_pair labels11 pairModel11_le_primeModel
    (transfer_of_regions labels11 ⟨33, by simp [labels11]⟩ region_transfer11) δ hδ

#print axioms pairModel_union
#print axioms transfer_union
#print axioms transfer_of_regions
#print axioms prime_transfer_of_pair
#print axioms pairModel11_le_primeModel
#print axioms region_transfer11
#print axioms prime_to_rough11_from_leaves
end
end LeanLab.Languasco2004.Feed564bPrime
