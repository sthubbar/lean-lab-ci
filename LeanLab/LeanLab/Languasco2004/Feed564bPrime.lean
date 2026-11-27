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
  use 1 / 100
  constructor
  · norm_num
  intro ε hε heps
  have hε₁ : ε < 1 / 100 := heps
  have hε_pos : 0 < ε := hε
  -- Choose N₀ large enough so that Y = localization N ε is large enough for all inequalities
  have h₁ : ∃ (N₀ : ℝ), ∀ (N : ℝ), N₀ ≤ N → ∀ (n : ℕ), n ∈ window N ε →
      pairModel labels11 N (localization N ε) n ≤ primeModel labels11 N (localization N ε) n := by
    -- For each region in labels11, the region conditions imply the clipping conditions for large Y
    -- We use the fact that labels11 is finite and take the maximum of the thresholds
    have h₂ : ∃ (Y₀ : ℝ), ∀ (Y : ℝ), Y₀ ≤ Y → ∀ (p q : ℕ), p.Prime → q.Prime →
        (∃ i ∈ (labels11 : Finset ℕ), regionIndex Y p q = i) →
        (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
        (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
      -- We prove this by considering each region in labels11 = {33, 36, 38, 40, 42, 46, 49}
      -- and finding a threshold Y₀ for each, then taking the maximum.
      have h₂₁ : ∃ (Y₀ : ℝ), ∀ (Y : ℝ), Y₀ ≤ Y → ∀ (p q : ℕ), p.Prime → q.Prime →
          (∃ i ∈ (labels11 : Finset ℕ), regionIndex Y p q = i) →
          (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
          (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
        -- Use the fact that for each region, the exponents satisfy the required inequalities for large Y
        -- We'll use a sufficiently large Y₀ that works for all regions
        use 1000000
        intro Y hY p q hp hq hregion
        have h₁ : Y ≥ 1000000 := hY
        have h₂ : 1 < (Y : ℝ) := by norm_num at h₁ ⊢ <;> linarith
        -- Extract the region index from the hypothesis
        obtain ⟨i, hi, hreg⟩ := hregion
        have hi' : i ∈ (labels11 : Finset ℕ) := hi
        have hreg' : regionIndex Y p q = i := hreg
        -- Since i ∈ labels11, we know i is one of 33, 36, 38, 40, 42, 46, 49
        have h₃ : i = 33 ∨ i = 36 ∨ i = 38 ∨ i = 40 ∨ i = 42 ∨ i = 46 ∨ i = 49 := by
          simp only [labels11, Finset.mem_insert, Finset.mem_singleton] at hi'
          tauto
        -- For each possible region, we use the regionIndex_eq_iff to get the region conditions
        -- and then verify the clipping conditions hold for large Y
        have h₄ : (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
            (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
          -- Use the fact that regionIndex Y p q = i gives us the region conditions
          have h₅ : regionIndex Y p q = i := hreg'
          have h₆ : ∃ (i : ℕ), i ∈ Set.Icc (1 : ℕ) 69 ∧
              (Y : ℝ) ^ (regionData i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (Y : ℝ) ^ (regionData i 1 : ℝ) ∧
              (p : ℝ) ^ (regionData i 2 : ℝ) * (Y : ℝ) ^ (regionData i 3 : ℝ) < (q : ℝ) ∧
              (q : ℝ) < (p : ℝ) ^ (regionData i 4 : ℝ) * (Y : ℝ) ^ (regionData i 5 : ℝ) := by
            by_cases h : ∃ (i : ℕ), i ∈ Set.Icc (1 : ℕ) 69 ∧
                (Y : ℝ) ^ (regionData i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (Y : ℝ) ^ (regionData i 1 : ℝ) ∧
                (p : ℝ) ^ (regionData i 2 : ℝ) * (Y : ℝ) ^ (regionData i 3 : ℝ) < (q : ℝ) ∧
                (q : ℝ) < (p : ℝ) ^ (regionData i 4 : ℝ) * (Y : ℝ) ^ (regionData i 5 : ℝ)
            · exact h
            · exfalso
              simp [regionIndex] at h₅
              <;> simp_all
          obtain ⟨i', hi', hp₁, hp₂, hq₁, hq₂⟩ := h₆
          have h₇ : i' = i := by
            have h₈ : regionIndex Y p q = i := hreg'
            have h₉ : regionIndex Y p q = i' := by
              simp [regionIndex, hi']
              <;> rfl
            linarith
          -- Now we have the region conditions for region i
          -- We need to check the clipping conditions for each possible i
          have h₈ : i = 33 ∨ i = 36 ∨ i = 38 ∨ i = 40 ∨ i = 42 ∨ i = 46 ∨ i = 49 := h₃
          rcases h₈ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          · -- Case i = 33
            have h₉ : i' = 33 := by linarith
            have h₁₀ : (Y : ℝ) ^ (regionData 33 0 : ℝ) < (p : ℝ) := hp₁
            have h₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (regionData 33 1 : ℝ) := hp₂
            have h₁₂ : (p : ℝ) ^ (regionData 33 2 : ℝ) * (Y : ℝ) ^ (regionData 33 3 : ℝ) < (q : ℝ) := hq₁
            have h₁₃ : (q : ℝ) < (p : ℝ) ^ (regionData 33 4 : ℝ) * (Y : ℝ) ^ (regionData 33 5 : ℝ) := hq₂
            have h₁₄ : (regionData 33 0 : ℝ) = (1649 / 4752 : ℝ) := by norm_num [regionData]
            have h₁₅ : (regionData 33 1 : ℝ) = (25 / 72 : ℝ) := by norm_num [regionData]
            have h₁₆ : (regionData 33 2 : ℝ) = (-70 / 59 : ℝ) := by norm_num [regionData]
            have h₁₇ : (regionData 33 3 : ℝ) = (34 / 59 : ℝ) := by norm_num [regionData]
            have h₁₈ : (regionData 33 4 : ℝ) = (-58 / 49 : ℝ) := by norm_num [regionData]
            have h₁₉ : (regionData 33 5 : ℝ) = (85 / 147 : ℝ) := by norm_num [regionData]
            rw [h₁₄] at h₁₀
            rw [h₁₅] at h₁₁
            rw [h₁₆, h₁₇] at h₁₂
            rw [h₁₈, h₁₉] at h₁₃
            have h₂₀ : (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) := by
              -- Y^(1649/4752) < p and 1649/4752 > 16/135, so Y^(16/135) < Y^(1649/4752) < p
              have h₂₀₁ : (Y : ℝ) ^ (16 / 135 : ℝ) < (Y : ℝ) ^ (1649 / 4752 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₁ : (p : ℝ) ≤ Real.sqrt (2 * Y) := by
              -- p ≤ Y^(25/72) and 25/72 < 1/2, so Y^(25/72) < sqrt(Y) < sqrt(2Y)
              have h₂₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (25 / 72 : ℝ) := h₁₁
              have h₂₁₂ : (Y : ℝ) ^ (25 / 72 : ℝ) ≤ Real.sqrt (2 * Y) := by
                have h₂₁₃ : (Y : ℝ) ^ (25 / 72 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                have h₂₁₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                  rw [Real.sqrt_eq_rpow]
                  <;> norm_num
                rw [h₂₁₄] at h₂₁₃
                have h₂₁₅ : Real.sqrt Y ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt (by positivity)
                linarith
              linarith
            have h₂₂ : (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) := by
              -- q > p^(-70/59) * Y^(34/59) ≥ Y^((25/72)*(-70/59) + 34/59) > Y^(16/135)
              have h₂₂₁ : (q : ℝ) > (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) := by linarith
              have h₂₂₂ : (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) ≥ (Y : ℝ) ^ ((25 / 72 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) := by
                have h₂₂₃ : (p : ℝ) ≤ (Y : ℝ) ^ (25 / 72 : ℝ) := h₁₁
                have h₂₂₄ : 0 < (p : ℝ) := by positivity
                have h₂₂₅ : 0 < (Y : ℝ) := by positivity
                have h₂₂₆ : (p : ℝ) ^ (-70 / 59 : ℝ) ≥ ((Y : ℝ) ^ (25 / 72 : ℝ)) ^ (-70 / 59 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by linarith) (by norm_num)
                calc
                  (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) ≥ ((Y : ℝ) ^ (25 / 72 : ℝ)) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) := by gcongr
                  _ = (Y : ℝ) ^ ((25 / 72 : ℝ) * (-70 / 59 : ℝ)) * (Y : ℝ) ^ (34 / 59 : ℝ) := by
                    rw [← Real.rpow_mul (by positivity)]
                    <;> ring_nf
                  _ = (Y : ℝ) ^ ((25 / 72 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) := by
                    rw [← Real.rpow_add (by positivity)]
                    <;> ring_nf
              have h₂₂₇ : (Y : ℝ) ^ ((25 / 72 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) > (Y : ℝ) ^ (16 / 135 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₃ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
              -- q < p^(-58/49) * Y^(85/147) < min(p, sqrt(2Y/p))
              have h₂₃₁ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
              have h₂₃₂ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                have h₂₃₃ : (p : ℝ) ≥ (Y : ℝ) ^ (1649 / 4752 : ℝ) := by linarith
                have h₂₃₄ : 0 < (p : ℝ) := by positivity
                have h₂₃₅ : 0 < (Y : ℝ) := by positivity
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                  have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₇]
                  have h₂₃₈ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (p : ℝ) := by
                    have h₂₃₉ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ (p : ℝ) ^ (58 / 49 : ℝ) := le_refl _
                    have h₂₄₀ : (p : ℝ) ≥ (Y : ℝ) ^ (1649 / 4752 : ℝ) := by linarith
                    have h₂₄₁ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ ((Y : ℝ) ^ (1649 / 4752 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (1649 / 4752 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply div_le_div_of_le_left (by positivity) (by positivity)
                      exact h₂₄₁
                    have h₂₄₃ : (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (1649 / 4752 : ℝ)) ^ (58 / 49 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((1649 / 4752 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_mul (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₃] at h₂₄₂
                    have h₂₄₄ : (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((1649 / 4752 : ℝ) * (58 / 49 : ℝ)) = (Y : ℝ) ^ ((85 / 147 : ℝ) - (1649 / 4752 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_sub (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₄] at h₂₄₂
                    have h₂₄₅ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (1649 / 4752 : ℝ) * (58 / 49 : ℝ)) ≤ (p : ℝ) := by
                      have h₂₄₆ : (85 / 147 : ℝ) - (1649 / 4752 : ℝ) * (58 / 49 : ℝ) < (1649 / 4752 : ℝ) := by norm_num
                      have h₂₄₇ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (1649 / 4752 : ℝ) * (58 / 49 : ℝ)) < (Y : ℝ) ^ (1649 / 4752 : ℝ) := by
                        apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₄₆ ⊢ <;> linarith)
                      have h₂₄₈ : (Y : ℝ) ^ (1649 / 4752 : ℝ) ≤ (p : ℝ) := by linarith
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₃ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                have h₂₃₄ : (p : ℝ) ≤ (Y : ℝ) ^ (25 / 72 : ℝ) := h₁₁
                have h₂₃₅ : 0 < (p : ℝ) := by positivity
                have h₂₃₆ : 0 < (Y : ℝ) := by positivity
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                  have h₂₃₈ : Real.sqrt (2 * Y / (p : ℝ)) = Real.sqrt (2 * Y / (p : ℝ)) := rfl
                  have h₂₃₉ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₉]
                  have h₂₄₀ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                    have h₂₄₁ : Real.sqrt (2 * Y / (p : ℝ)) ≥ 0 := Real.sqrt_nonneg _
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≥ 0 := by positivity
                    have h₂₄₃ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 ≤ (2 * Y / (p : ℝ)) := by
                      have h₂₄₄ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 = (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) := by
                        field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                        <;> field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                      rw [h₂₄₄]
                      have h₂₄₅ : (p : ℝ) ≥ (Y : ℝ) ^ (1649 / 4752 : ℝ) := by linarith
                      have h₂₄₆ : (p : ℝ) ≤ (Y : ℝ) ^ (25 / 72 : ℝ) := h₁₁
                      have h₂₄₇ : (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) ≤ (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (1649 / 4752 : ℝ)) ^ (116 / 49 : ℝ) := by
                        apply div_le_div_of_le_left (by positivity) (by positivity)
                        have h₂₄₈ : (p : ℝ) ^ (116 / 49 : ℝ) ≥ ((Y : ℝ) ^ (1649 / 4752 : ℝ)) ^ (116 / 49 : ℝ) := by
                          apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                        linarith
                      have h₂₄₉ : (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (1649 / 4752 : ℝ)) ^ (116 / 49 : ℝ) = (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((1649 / 4752 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_mul (by positivity)]
                        <;> ring_nf
                      rw [h₂₄₉] at h₂₄₇
                      have h₂₅₀ : (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((1649 / 4752 : ℝ) * (116 / 49 : ℝ)) = (Y : ℝ) ^ ((170 / 147 : ℝ) - (1649 / 4752 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_sub (by positivity)]
                        <;> ring_nf
                      rw [h₂₅₀] at h₂₄₇
                      have h₂₅₁ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (1649 / 4752 : ℝ) * (116 / 49 : ℝ)) ≤ 2 * Y / (p : ℝ) := by
                        have h₂₅₂ : (170 / 147 : ℝ) - (1649 / 4752 : ℝ) * (116 / 49 : ℝ) < (1 / 2 : ℝ) := by norm_num
                        have h₂₅₃ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (1649 / 4752 : ℝ) * (116 / 49 : ℝ)) < (Y : ℝ) ^ (1 / 2 : ℝ) := by
                          apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₅₂ ⊢ <;> linarith)
                        have h₂₅₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                          rw [Real.sqrt_eq_rpow]
                          <;> norm_num
                        rw [h₂₅₄] at h₂₅₃
                        have h₂₅₅ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                          have h₂₅₆ : (p : ℝ) ≤ (Y : ℝ) ^ (25 / 72 : ℝ) := h₁₁
                          have h₂₅₇ : (Y : ℝ) ^ (25 / 72 : ℝ) ≤ (Y : ℝ) := by
                            apply Real.rpow_le_rpow (by linarith) (by norm_num)
                          have h₂₅₈ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                          have h₂₅₉ : 0 < (p : ℝ) := by positivity
                          have h₂₆₀ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                            have h₂₆₁ : Real.sqrt Y = (Y : ℝ) ^ (1 / 2 : ℝ) := by
                              rw [Real.sqrt_eq_rpow]
                              <;> norm_num
                            rw [h₂₆₁]
                            have h₂₆₂ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * Y / (p : ℝ) := by
                              have h₂₆₃ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                              have h₂₆₄ : 0 < (p : ℝ) := by positivity
                              have h₂₆₅ : 2 * Y / (p : ℝ) ≥ 2 * Y / (Y : ℝ) := by
                                apply div_le_div_of_le_left (by positivity) (by positivity)
                                linarith
                              have h₂₆₆ : 2 * Y / (Y : ℝ) = 2 := by
                                field_simp [h₂₃₆.ne']
                                <;> ring_nf
                              have h₂₆₇ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
                                have h₂₆₈ : (Y : ℝ) ≥ 1000000 := by exact_mod_cast h₁
                                have h₂₆₉ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ (Y : ℝ) := by
                                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                                have h₂₇₀ : (Y : ℝ) ≤ 2 * (Y : ℝ) := by linarith
                                nlinarith [Real.sqrt_nonneg (Y : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (Y : ℝ))]
                              linarith
                            linarith
                          linarith
                        linarith
                      linarith
                    have h₂₄₅ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                      apply Real.le_sqrt_of_sq_le
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₄ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
                have h₂₃₅ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := h₂₃₂
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := h₂₃₃
                have h₂₃₈ : (q : ℝ) < (p : ℝ) := by linarith
                have h₂₃₉ : (q : ℝ) < Real.sqrt (2 * Y / (p : ℝ)) := by linarith
                rw [min_lt_iff]
                exact ⟨h₂₃₈, h₂₃₉⟩
              exact h₂₃₄
            exact ⟨h₂₀, h₂₁, h₂₂, h₂₃⟩
          · -- Case i = 36
            have h₉ : i' = 36 := by linarith
            have h₁₀ : (Y : ℝ) ^ (regionData 36 0 : ℝ) < (p : ℝ) := hp₁
            have h₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (regionData 36 1 : ℝ) := hp₂
            have h₁₂ : (p : ℝ) ^ (regionData 36 2 : ℝ) * (Y : ℝ) ^ (regionData 36 3 : ℝ) < (q : ℝ) := hq₁
            have h₁₃ : (q : ℝ) < (p : ℝ) ^ (regionData 36 4 : ℝ) * (Y : ℝ) ^ (regionData 36 5 : ℝ) := hq₂
            have h₁₄ : (regionData 36 0 : ℝ) = (25 / 72 : ℝ) := by norm_num [regionData]
            have h₁₅ : (regionData 36 1 : ℝ) = (10 / 27 : ℝ) := by norm_num [regionData]
            have h₁₆ : (regionData 36 2 : ℝ) = (-70 / 59 : ℝ) := by norm_num [regionData]
            have h₁₇ : (regionData 36 3 : ℝ) = (34 / 59 : ℝ) := by norm_num [regionData]
            have h₁₈ : (regionData 36 4 : ℝ) = (-58 / 49 : ℝ) := by norm_num [regionData]
            have h₁₉ : (regionData 36 5 : ℝ) = (85 / 147 : ℝ) := by norm_num [regionData]
            rw [h₁₄] at h₁₀
            rw [h₁₅] at h₁₁
            rw [h₁₆, h₁₇] at h₁₂
            rw [h₁₈, h₁₉] at h₁₃
            have h₂₀ : (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) := by
              have h₂₀₁ : (Y : ℝ) ^ (16 / 135 : ℝ) < (Y : ℝ) ^ (25 / 72 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₁ : (p : ℝ) ≤ Real.sqrt (2 * Y) := by
              have h₂₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (10 / 27 : ℝ) := h₁₁
              have h₂₁₂ : (Y : ℝ) ^ (10 / 27 : ℝ) ≤ Real.sqrt (2 * Y) := by
                have h₂₁₃ : (Y : ℝ) ^ (10 / 27 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                have h₂₁₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                  rw [Real.sqrt_eq_rpow]
                  <;> norm_num
                rw [h₂₁₄] at h₂₁₃
                have h₂₁₅ : Real.sqrt Y ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt (by positivity)
                linarith
              linarith
            have h₂₂ : (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) := by
              have h₂₂₁ : (q : ℝ) > (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) := by linarith
              have h₂₂₂ : (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) ≥ (Y : ℝ) ^ ((10 / 27 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) := by
                have h₂₂₃ : (p : ℝ) ≤ (Y : ℝ) ^ (10 / 27 : ℝ) := h₁₁
                have h₂₂₄ : 0 < (p : ℝ) := by positivity
                have h₂₂₅ : 0 < (Y : ℝ) := by positivity
                have h₂₂₆ : (p : ℝ) ^ (-70 / 59 : ℝ) ≥ ((Y : ℝ) ^ (10 / 27 : ℝ)) ^ (-70 / 59 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by linarith) (by norm_num)
                calc
                  (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) ≥ ((Y : ℝ) ^ (10 / 27 : ℝ)) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) := by gcongr
                  _ = (Y : ℝ) ^ ((10 / 27 : ℝ) * (-70 / 59 : ℝ)) * (Y : ℝ) ^ (34 / 59 : ℝ) := by
                    rw [← Real.rpow_mul (by positivity)]
                    <;> ring_nf
                  _ = (Y : ℝ) ^ ((10 / 27 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) := by
                    rw [← Real.rpow_add (by positivity)]
                    <;> ring_nf
              have h₂₂₇ : (Y : ℝ) ^ ((10 / 27 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) > (Y : ℝ) ^ (16 / 135 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₃ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
              have h₂₃₁ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
              have h₂₃₂ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                have h₂₃₃ : (p : ℝ) ≥ (Y : ℝ) ^ (25 / 72 : ℝ) := by linarith
                have h₂₃₄ : 0 < (p : ℝ) := by positivity
                have h₂₃₅ : 0 < (Y : ℝ) := by positivity
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                  have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₇]
                  have h₂₃₈ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (p : ℝ) := by
                    have h₂₃₉ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ (p : ℝ) ^ (58 / 49 : ℝ) := le_refl _
                    have h₂₄₀ : (p : ℝ) ≥ (Y : ℝ) ^ (25 / 72 : ℝ) := by linarith
                    have h₂₄₁ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ ((Y : ℝ) ^ (25 / 72 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (25 / 72 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply div_le_div_of_le_left (by positivity) (by positivity)
                      exact h₂₄₁
                    have h₂₄₃ : (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (25 / 72 : ℝ)) ^ (58 / 49 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((25 / 72 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_mul (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₃] at h₂₄₂
                    have h₂₄₄ : (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((25 / 72 : ℝ) * (58 / 49 : ℝ)) = (Y : ℝ) ^ ((85 / 147 : ℝ) - (25 / 72 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_sub (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₄] at h₂₄₂
                    have h₂₄₅ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (25 / 72 : ℝ) * (58 / 49 : ℝ)) ≤ (p : ℝ) := by
                      have h₂₄₆ : (85 / 147 : ℝ) - (25 / 72 : ℝ) * (58 / 49 : ℝ) < (25 / 72 : ℝ) := by norm_num
                      have h₂₄₇ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (25 / 72 : ℝ) * (58 / 49 : ℝ)) < (Y : ℝ) ^ (25 / 72 : ℝ) := by
                        apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₄₆ ⊢ <;> linarith)
                      have h₂₄₈ : (Y : ℝ) ^ (25 / 72 : ℝ) ≤ (p : ℝ) := by linarith
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₃ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                have h₂₃₄ : (p : ℝ) ≤ (Y : ℝ) ^ (10 / 27 : ℝ) := h₁₁
                have h₂₃₅ : 0 < (p : ℝ) := by positivity
                have h₂₃₆ : 0 < (Y : ℝ) := by positivity
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                  have h₂₃₈ : Real.sqrt (2 * Y / (p : ℝ)) = Real.sqrt (2 * Y / (p : ℝ)) := rfl
                  have h₂₃₉ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₉]
                  have h₂₄₀ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                    have h₂₄₁ : Real.sqrt (2 * Y / (p : ℝ)) ≥ 0 := Real.sqrt_nonneg _
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≥ 0 := by positivity
                    have h₂₄₃ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 ≤ (2 * Y / (p : ℝ)) := by
                      have h₂₄₄ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 = (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) := by
                        field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                        <;> field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                      rw [h₂₄₄]
                      have h₂₄₅ : (p : ℝ) ≥ (Y : ℝ) ^ (25 / 72 : ℝ) := by linarith
                      have h₂₄₆ : (p : ℝ) ≤ (Y : ℝ) ^ (10 / 27 : ℝ) := h₁₁
                      have h₂₄₇ : (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) ≤ (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (25 / 72 : ℝ)) ^ (116 / 49 : ℝ) := by
                        apply div_le_div_of_le_left (by positivity) (by positivity)
                        have h₂₄₈ : (p : ℝ) ^ (116 / 49 : ℝ) ≥ ((Y : ℝ) ^ (25 / 72 : ℝ)) ^ (116 / 49 : ℝ) := by
                          apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                        linarith
                      have h₂₄₉ : (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (25 / 72 : ℝ)) ^ (116 / 49 : ℝ) = (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((25 / 72 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_mul (by positivity)]
                        <;> ring_nf
                      rw [h₂₄₉] at h₂₄₇
                      have h₂₅₀ : (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((25 / 72 : ℝ) * (116 / 49 : ℝ)) = (Y : ℝ) ^ ((170 / 147 : ℝ) - (25 / 72 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_sub (by positivity)]
                        <;> ring_nf
                      rw [h₂₅₀] at h₂₄₇
                      have h₂₅₁ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (25 / 72 : ℝ) * (116 / 49 : ℝ)) ≤ 2 * Y / (p : ℝ) := by
                        have h₂₅₂ : (170 / 147 : ℝ) - (25 / 72 : ℝ) * (116 / 49 : ℝ) < (1 / 2 : ℝ) := by norm_num
                        have h₂₅₃ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (25 / 72 : ℝ) * (116 / 49 : ℝ)) < (Y : ℝ) ^ (1 / 2 : ℝ) := by
                          apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₅₂ ⊢ <;> linarith)
                        have h₂₅₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                          rw [Real.sqrt_eq_rpow]
                          <;> norm_num
                        rw [h₂₅₄] at h₂₅₃
                        have h₂₅₅ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                          have h₂₅₆ : (p : ℝ) ≤ (Y : ℝ) ^ (10 / 27 : ℝ) := h₁₁
                          have h₂₅₇ : (Y : ℝ) ^ (10 / 27 : ℝ) ≤ (Y : ℝ) := by
                            apply Real.rpow_le_rpow (by linarith) (by norm_num)
                          have h₂₅₈ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                          have h₂₅₉ : 0 < (p : ℝ) := by positivity
                          have h₂₆₀ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                            have h₂₆₁ : Real.sqrt Y = (Y : ℝ) ^ (1 / 2 : ℝ) := by
                              rw [Real.sqrt_eq_rpow]
                              <;> norm_num
                            rw [h₂₆₁]
                            have h₂₆₂ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * Y / (p : ℝ) := by
                              have h₂₆₃ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                              have h₂₆₄ : 0 < (p : ℝ) := by positivity
                              have h₂₆₅ : 2 * Y / (p : ℝ) ≥ 2 * Y / (Y : ℝ) := by
                                apply div_le_div_of_le_left (by positivity) (by positivity)
                                linarith
                              have h₂₆₆ : 2 * Y / (Y : ℝ) = 2 := by
                                field_simp [h₂₃₆.ne']
                                <;> ring_nf
                              have h₂₆₇ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
                                have h₂₆₈ : (Y : ℝ) ≥ 1000000 := by exact_mod_cast h₁
                                have h₂₆₉ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ (Y : ℝ) := by
                                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                                have h₂₇₀ : (Y : ℝ) ≤ 2 * (Y : ℝ) := by linarith
                                nlinarith [Real.sqrt_nonneg (Y : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (Y : ℝ))]
                              linarith
                            linarith
                          linarith
                        linarith
                      linarith
                    have h₂₄₅ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                      apply Real.le_sqrt_of_sq_le
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₄ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
                have h₂₃₅ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := h₂₃₂
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := h₂₃₃
                have h₂₃₈ : (q : ℝ) < (p : ℝ) := by linarith
                have h₂₃₉ : (q : ℝ) < Real.sqrt (2 * Y / (p : ℝ)) := by linarith
                rw [min_lt_iff]
                exact ⟨h₂₃₈, h₂₃₉⟩
              exact h₂₃₄
            exact ⟨h₂₀, h₂₁, h₂₂, h₂₃⟩
          · -- Case i = 38
            have h₉ : i' = 38 := by linarith
            have h₁₀ : (Y : ℝ) ^ (regionData 38 0 : ℝ) < (p : ℝ) := hp₁
            have h₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (regionData 38 1 : ℝ) := hp₂
            have h₁₂ : (p : ℝ) ^ (regionData 38 2 : ℝ) * (Y : ℝ) ^ (regionData 38 3 : ℝ) < (q : ℝ) := hq₁
            have h₁₃ : (q : ℝ) < (p : ℝ) ^ (regionData 38 4 : ℝ) * (Y : ℝ) ^ (regionData 38 5 : ℝ) := hq₂
            have h₁₄ : (regionData 38 0 : ℝ) = (10 / 27 : ℝ) := by norm_num [regionData]
            have h₁₅ : (regionData 38 1 : ℝ) = (617 / 1620 : ℝ) := by norm_num [regionData]
            have h₁₆ : (regionData 38 2 : ℝ) = (-70 / 59 : ℝ) := by norm_num [regionData]
            have h₁₇ : (regionData 38 3 : ℝ) = (34 / 59 : ℝ) := by norm_num [regionData]
            have h₁₈ : (regionData 38 4 : ℝ) = (-58 / 49 : ℝ) := by norm_num [regionData]
            have h₁₉ : (regionData 38 5 : ℝ) = (85 / 147 : ℝ) := by norm_num [regionData]
            rw [h₁₄] at h₁₀
            rw [h₁₅] at h₁₁
            rw [h₁₆, h₁₇] at h₁₂
            rw [h₁₈, h₁₉] at h₁₃
            have h₂₀ : (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) := by
              have h₂₀₁ : (Y : ℝ) ^ (16 / 135 : ℝ) < (Y : ℝ) ^ (10 / 27 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₁ : (p : ℝ) ≤ Real.sqrt (2 * Y) := by
              have h₂₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (617 / 1620 : ℝ) := h₁₁
              have h₂₁₂ : (Y : ℝ) ^ (617 / 1620 : ℝ) ≤ Real.sqrt (2 * Y) := by
                have h₂₁₃ : (Y : ℝ) ^ (617 / 1620 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                have h₂₁₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                  rw [Real.sqrt_eq_rpow]
                  <;> norm_num
                rw [h₂₁₄] at h₂₁₃
                have h₂₁₅ : Real.sqrt Y ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt (by positivity)
                linarith
              linarith
            have h₂₂ : (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) := by
              have h₂₂₁ : (q : ℝ) > (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) := by linarith
              have h₂₂₂ : (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) ≥ (Y : ℝ) ^ ((617 / 1620 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) := by
                have h₂₂₃ : (p : ℝ) ≤ (Y : ℝ) ^ (617 / 1620 : ℝ) := h₁₁
                have h₂₂₄ : 0 < (p : ℝ) := by positivity
                have h₂₂₅ : 0 < (Y : ℝ) := by positivity
                have h₂₂₆ : (p : ℝ) ^ (-70 / 59 : ℝ) ≥ ((Y : ℝ) ^ (617 / 1620 : ℝ)) ^ (-70 / 59 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by linarith) (by norm_num)
                calc
                  (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) ≥ ((Y : ℝ) ^ (617 / 1620 : ℝ)) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) := by gcongr
                  _ = (Y : ℝ) ^ ((617 / 1620 : ℝ) * (-70 / 59 : ℝ)) * (Y : ℝ) ^ (34 / 59 : ℝ) := by
                    rw [← Real.rpow_mul (by positivity)]
                    <;> ring_nf
                  _ = (Y : ℝ) ^ ((617 / 1620 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) := by
                    rw [← Real.rpow_add (by positivity)]
                    <;> ring_nf
              have h₂₂₇ : (Y : ℝ) ^ ((617 / 1620 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) > (Y : ℝ) ^ (16 / 135 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₃ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
              have h₂₃₁ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
              have h₂₃₂ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                have h₂₃₃ : (p : ℝ) ≥ (Y : ℝ) ^ (10 / 27 : ℝ) := by linarith
                have h₂₃₄ : 0 < (p : ℝ) := by positivity
                have h₂₃₅ : 0 < (Y : ℝ) := by positivity
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                  have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₇]
                  have h₂₃₈ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (p : ℝ) := by
                    have h₂₃₉ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ (p : ℝ) ^ (58 / 49 : ℝ) := le_refl _
                    have h₂₄₀ : (p : ℝ) ≥ (Y : ℝ) ^ (10 / 27 : ℝ) := by linarith
                    have h₂₄₁ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ ((Y : ℝ) ^ (10 / 27 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (10 / 27 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply div_le_div_of_le_left (by positivity) (by positivity)
                      exact h₂₄₁
                    have h₂₄₃ : (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (10 / 27 : ℝ)) ^ (58 / 49 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((10 / 27 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_mul (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₃] at h₂₄₂
                    have h₂₄₄ : (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((10 / 27 : ℝ) * (58 / 49 : ℝ)) = (Y : ℝ) ^ ((85 / 147 : ℝ) - (10 / 27 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_sub (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₄] at h₂₄₂
                    have h₂₄₅ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (10 / 27 : ℝ) * (58 / 49 : ℝ)) ≤ (p : ℝ) := by
                      have h₂₄₆ : (85 / 147 : ℝ) - (10 / 27 : ℝ) * (58 / 49 : ℝ) < (10 / 27 : ℝ) := by norm_num
                      have h₂₄₇ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (10 / 27 : ℝ) * (58 / 49 : ℝ)) < (Y : ℝ) ^ (10 / 27 : ℝ) := by
                        apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₄₆ ⊢ <;> linarith)
                      have h₂₄₈ : (Y : ℝ) ^ (10 / 27 : ℝ) ≤ (p : ℝ) := by linarith
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₃ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                have h₂₃₄ : (p : ℝ) ≤ (Y : ℝ) ^ (617 / 1620 : ℝ) := h₁₁
                have h₂₃₅ : 0 < (p : ℝ) := by positivity
                have h₂₃₆ : 0 < (Y : ℝ) := by positivity
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                  have h₂₃₈ : Real.sqrt (2 * Y / (p : ℝ)) = Real.sqrt (2 * Y / (p : ℝ)) := rfl
                  have h₂₃₉ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₉]
                  have h₂₄₀ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                    have h₂₄₁ : Real.sqrt (2 * Y / (p : ℝ)) ≥ 0 := Real.sqrt_nonneg _
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≥ 0 := by positivity
                    have h₂₄₃ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 ≤ (2 * Y / (p : ℝ)) := by
                      have h₂₄₄ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 = (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) := by
                        field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                        <;> field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                      rw [h₂₄₄]
                      have h₂₄₅ : (p : ℝ) ≥ (Y : ℝ) ^ (10 / 27 : ℝ) := by linarith
                      have h₂₄₆ : (p : ℝ) ≤ (Y : ℝ) ^ (617 / 1620 : ℝ) := h₁₁
                      have h₂₄₇ : (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) ≤ (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (10 / 27 : ℝ)) ^ (116 / 49 : ℝ) := by
                        apply div_le_div_of_le_left (by positivity) (by positivity)
                        have h₂₄₈ : (p : ℝ) ^ (116 / 49 : ℝ) ≥ ((Y : ℝ) ^ (10 / 27 : ℝ)) ^ (116 / 49 : ℝ) := by
                          apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                        linarith
                      have h₂₄₉ : (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (10 / 27 : ℝ)) ^ (116 / 49 : ℝ) = (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((10 / 27 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_mul (by positivity)]
                        <;> ring_nf
                      rw [h₂₄₉] at h₂₄₇
                      have h₂₅₀ : (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((10 / 27 : ℝ) * (116 / 49 : ℝ)) = (Y : ℝ) ^ ((170 / 147 : ℝ) - (10 / 27 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_sub (by positivity)]
                        <;> ring_nf
                      rw [h₂₅₀] at h₂₄₇
                      have h₂₅₁ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (10 / 27 : ℝ) * (116 / 49 : ℝ)) ≤ 2 * Y / (p : ℝ) := by
                        have h₂₅₂ : (170 / 147 : ℝ) - (10 / 27 : ℝ) * (116 / 49 : ℝ) < (1 / 2 : ℝ) := by norm_num
                        have h₂₅₃ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (10 / 27 : ℝ) * (116 / 49 : ℝ)) < (Y : ℝ) ^ (1 / 2 : ℝ) := by
                          apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₅₂ ⊢ <;> linarith)
                        have h₂₅₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                          rw [Real.sqrt_eq_rpow]
                          <;> norm_num
                        rw [h₂₅₄] at h₂₅₃
                        have h₂₅₅ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                          have h₂₅₆ : (p : ℝ) ≤ (Y : ℝ) ^ (617 / 1620 : ℝ) := h₁₁
                          have h₂₅₇ : (Y : ℝ) ^ (617 / 1620 : ℝ) ≤ (Y : ℝ) := by
                            apply Real.rpow_le_rpow (by linarith) (by norm_num)
                          have h₂₅₈ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                          have h₂₅₉ : 0 < (p : ℝ) := by positivity
                          have h₂₆₀ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                            have h₂₆₁ : Real.sqrt Y = (Y : ℝ) ^ (1 / 2 : ℝ) := by
                              rw [Real.sqrt_eq_rpow]
                              <;> norm_num
                            rw [h₂₆₁]
                            have h₂₆₂ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * Y / (p : ℝ) := by
                              have h₂₆₃ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                              have h₂₆₄ : 0 < (p : ℝ) := by positivity
                              have h₂₆₅ : 2 * Y / (p : ℝ) ≥ 2 * Y / (Y : ℝ) := by
                                apply div_le_div_of_le_left (by positivity) (by positivity)
                                linarith
                              have h₂₆₆ : 2 * Y / (Y : ℝ) = 2 := by
                                field_simp [h₂₃₆.ne']
                                <;> ring_nf
                              have h₂₆₇ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
                                have h₂₆₈ : (Y : ℝ) ≥ 1000000 := by exact_mod_cast h₁
                                have h₂₆₉ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ (Y : ℝ) := by
                                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                                have h₂₇₀ : (Y : ℝ) ≤ 2 * (Y : ℝ) := by linarith
                                nlinarith [Real.sqrt_nonneg (Y : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (Y : ℝ))]
                              linarith
                            linarith
                          linarith
                        linarith
                      linarith
                    have h₂₄₅ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                      apply Real.le_sqrt_of_sq_le
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₄ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
                have h₂₃₅ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := h₂₃₂
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := h₂₃₃
                have h₂₃₈ : (q : ℝ) < (p : ℝ) := by linarith
                have h₂₃₉ : (q : ℝ) < Real.sqrt (2 * Y / (p : ℝ)) := by linarith
                rw [min_lt_iff]
                exact ⟨h₂₃₈, h₂₃₉⟩
              exact h₂₃₄
            exact ⟨h₂₀, h₂₁, h₂₂, h₂₃⟩
          · -- Case i = 40
            have h₉ : i' = 40 := by linarith
            have h₁₀ : (Y : ℝ) ^ (regionData 40 0 : ℝ) < (p : ℝ) := hp₁
            have h₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (regionData 40 1 : ℝ) := hp₂
            have h₁₂ : (p : ℝ) ^ (regionData 40 2 : ℝ) * (Y : ℝ) ^ (regionData 40 3 : ℝ) < (q : ℝ) := hq₁
            have h₁₃ : (q : ℝ) < (p : ℝ) ^ (regionData 40 4 : ℝ) * (Y : ℝ) ^ (regionData 40 5 : ℝ) := hq₂
            have h₁₄ : (regionData 40 0 : ℝ) = (617 / 1620 : ℝ) := by norm_num [regionData]
            have h₁₅ : (regionData 40 1 : ℝ) = (1823 / 4725 : ℝ) := by norm_num [regionData]
            have h₁₆ : (regionData 40 2 : ℝ) = (-70 / 59 : ℝ) := by norm_num [regionData]
            have h₁₇ : (regionData 40 3 : ℝ) = (34 / 59 : ℝ) := by norm_num [regionData]
            have h₁₈ : (regionData 40 4 : ℝ) = (-58 / 49 : ℝ) := by norm_num [regionData]
            have h₁₉ : (regionData 40 5 : ℝ) = (85 / 147 : ℝ) := by norm_num [regionData]
            rw [h₁₄] at h₁₀
            rw [h₁₅] at h₁₁
            rw [h₁₆, h₁₇] at h₁₂
            rw [h₁₈, h₁₉] at h₁₃
            have h₂₀ : (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) := by
              have h₂₀₁ : (Y : ℝ) ^ (16 / 135 : ℝ) < (Y : ℝ) ^ (617 / 1620 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₁ : (p : ℝ) ≤ Real.sqrt (2 * Y) := by
              have h₂₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (1823 / 4725 : ℝ) := h₁₁
              have h₂₁₂ : (Y : ℝ) ^ (1823 / 4725 : ℝ) ≤ Real.sqrt (2 * Y) := by
                have h₂₁₃ : (Y : ℝ) ^ (1823 / 4725 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                have h₂₁₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                  rw [Real.sqrt_eq_rpow]
                  <;> norm_num
                rw [h₂₁₄] at h₂₁₃
                have h₂₁₅ : Real.sqrt Y ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt (by positivity)
                linarith
              linarith
            have h₂₂ : (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) := by
              have h₂₂₁ : (q : ℝ) > (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) := by linarith
              have h₂₂₂ : (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) ≥ (Y : ℝ) ^ ((1823 / 4725 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) := by
                have h₂₂₃ : (p : ℝ) ≤ (Y : ℝ) ^ (1823 / 4725 : ℝ) := h₁₁
                have h₂₂₄ : 0 < (p : ℝ) := by positivity
                have h₂₂₅ : 0 < (Y : ℝ) := by positivity
                have h₂₂₆ : (p : ℝ) ^ (-70 / 59 : ℝ) ≥ ((Y : ℝ) ^ (1823 / 4725 : ℝ)) ^ (-70 / 59 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by linarith) (by norm_num)
                calc
                  (p : ℝ) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) ≥ ((Y : ℝ) ^ (1823 / 4725 : ℝ)) ^ (-70 / 59 : ℝ) * (Y : ℝ) ^ (34 / 59 : ℝ) := by gcongr
                  _ = (Y : ℝ) ^ ((1823 / 4725 : ℝ) * (-70 / 59 : ℝ)) * (Y : ℝ) ^ (34 / 59 : ℝ) := by
                    rw [← Real.rpow_mul (by positivity)]
                    <;> ring_nf
                  _ = (Y : ℝ) ^ ((1823 / 4725 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) := by
                    rw [← Real.rpow_add (by positivity)]
                    <;> ring_nf
              have h₂₂₇ : (Y : ℝ) ^ ((1823 / 4725 : ℝ) * (-70 / 59 : ℝ) + (34 / 59 : ℝ)) > (Y : ℝ) ^ (16 / 135 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₃ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
              have h₂₃₁ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
              have h₂₃₂ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                have h₂₃₃ : (p : ℝ) ≥ (Y : ℝ) ^ (617 / 1620 : ℝ) := by linarith
                have h₂₃₄ : 0 < (p : ℝ) := by positivity
                have h₂₃₅ : 0 < (Y : ℝ) := by positivity
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                  have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₇]
                  have h₂₃₈ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (p : ℝ) := by
                    have h₂₃₉ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ (p : ℝ) ^ (58 / 49 : ℝ) := le_refl _
                    have h₂₄₀ : (p : ℝ) ≥ (Y : ℝ) ^ (617 / 1620 : ℝ) := by linarith
                    have h₂₄₁ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ ((Y : ℝ) ^ (617 / 1620 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (617 / 1620 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply div_le_div_of_le_left (by positivity) (by positivity)
                      exact h₂₄₁
                    have h₂₄₃ : (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (617 / 1620 : ℝ)) ^ (58 / 49 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((617 / 1620 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_mul (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₃] at h₂₄₂
                    have h₂₄₄ : (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((617 / 1620 : ℝ) * (58 / 49 : ℝ)) = (Y : ℝ) ^ ((85 / 147 : ℝ) - (617 / 1620 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_sub (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₄] at h₂₄₂
                    have h₂₄₅ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (617 / 1620 : ℝ) * (58 / 49 : ℝ)) ≤ (p : ℝ) := by
                      have h₂₄₆ : (85 / 147 : ℝ) - (617 / 1620 : ℝ) * (58 / 49 : ℝ) < (617 / 1620 : ℝ) := by norm_num
                      have h₂₄₇ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (617 / 1620 : ℝ) * (58 / 49 : ℝ)) < (Y : ℝ) ^ (617 / 1620 : ℝ) := by
                        apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₄₆ ⊢ <;> linarith)
                      have h₂₄₈ : (Y : ℝ) ^ (617 / 1620 : ℝ) ≤ (p : ℝ) := by linarith
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₃ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                have h₂₃₄ : (p : ℝ) ≤ (Y : ℝ) ^ (1823 / 4725 : ℝ) := h₁₁
                have h₂₃₅ : 0 < (p : ℝ) := by positivity
                have h₂₃₆ : 0 < (Y : ℝ) := by positivity
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                  have h₂₃₈ : Real.sqrt (2 * Y / (p : ℝ)) = Real.sqrt (2 * Y / (p : ℝ)) := rfl
                  have h₂₃₉ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₉]
                  have h₂₄₀ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                    have h₂₄₁ : Real.sqrt (2 * Y / (p : ℝ)) ≥ 0 := Real.sqrt_nonneg _
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≥ 0 := by positivity
                    have h₂₄₃ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 ≤ (2 * Y / (p : ℝ)) := by
                      have h₂₄₄ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 = (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) := by
                        field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                        <;> field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                      rw [h₂₄₄]
                      have h₂₄₅ : (p : ℝ) ≥ (Y : ℝ) ^ (617 / 1620 : ℝ) := by linarith
                      have h₂₄₆ : (p : ℝ) ≤ (Y : ℝ) ^ (1823 / 4725 : ℝ) := h₁₁
                      have h₂₄₇ : (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) ≤ (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (617 / 1620 : ℝ)) ^ (116 / 49 : ℝ) := by
                        apply div_le_div_of_le_left (by positivity) (by positivity)
                        have h₂₄₈ : (p : ℝ) ^ (116 / 49 : ℝ) ≥ ((Y : ℝ) ^ (617 / 1620 : ℝ)) ^ (116 / 49 : ℝ) := by
                          apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                        linarith
                      have h₂₄₉ : (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (617 / 1620 : ℝ)) ^ (116 / 49 : ℝ) = (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((617 / 1620 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_mul (by positivity)]
                        <;> ring_nf
                      rw [h₂₄₉] at h₂₄₇
                      have h₂₅₀ : (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((617 / 1620 : ℝ) * (116 / 49 : ℝ)) = (Y : ℝ) ^ ((170 / 147 : ℝ) - (617 / 1620 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_sub (by positivity)]
                        <;> ring_nf
                      rw [h₂₅₀] at h₂₄₇
                      have h₂₅₁ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (617 / 1620 : ℝ) * (116 / 49 : ℝ)) ≤ 2 * Y / (p : ℝ) := by
                        have h₂₅₂ : (170 / 147 : ℝ) - (617 / 1620 : ℝ) * (116 / 49 : ℝ) < (1 / 2 : ℝ) := by norm_num
                        have h₂₅₃ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (617 / 1620 : ℝ) * (116 / 49 : ℝ)) < (Y : ℝ) ^ (1 / 2 : ℝ) := by
                          apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₅₂ ⊢ <;> linarith)
                        have h₂₅₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                          rw [Real.sqrt_eq_rpow]
                          <;> norm_num
                        rw [h₂₅₄] at h₂₅₃
                        have h₂₅₅ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                          have h₂₅₆ : (p : ℝ) ≤ (Y : ℝ) ^ (1823 / 4725 : ℝ) := h₁₁
                          have h₂₅₇ : (Y : ℝ) ^ (1823 / 4725 : ℝ) ≤ (Y : ℝ) := by
                            apply Real.rpow_le_rpow (by linarith) (by norm_num)
                          have h₂₅₈ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                          have h₂₅₉ : 0 < (p : ℝ) := by positivity
                          have h₂₆₀ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                            have h₂₆₁ : Real.sqrt Y = (Y : ℝ) ^ (1 / 2 : ℝ) := by
                              rw [Real.sqrt_eq_rpow]
                              <;> norm_num
                            rw [h₂₆₁]
                            have h₂₆₂ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * Y / (p : ℝ) := by
                              have h₂₆₃ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                              have h₂₆₄ : 0 < (p : ℝ) := by positivity
                              have h₂₆₅ : 2 * Y / (p : ℝ) ≥ 2 * Y / (Y : ℝ) := by
                                apply div_le_div_of_le_left (by positivity) (by positivity)
                                linarith
                              have h₂₆₆ : 2 * Y / (Y : ℝ) = 2 := by
                                field_simp [h₂₃₆.ne']
                                <;> ring_nf
                              have h₂₆₇ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
                                have h₂₆₈ : (Y : ℝ) ≥ 1000000 := by exact_mod_cast h₁
                                have h₂₆₉ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ (Y : ℝ) := by
                                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                                have h₂₇₀ : (Y : ℝ) ≤ 2 * (Y : ℝ) := by linarith
                                nlinarith [Real.sqrt_nonneg (Y : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (Y : ℝ))]
                              linarith
                            linarith
                          linarith
                        linarith
                      linarith
                    have h₂₄₅ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                      apply Real.le_sqrt_of_sq_le
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₄ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
                have h₂₃₅ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := h₂₃₂
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := h₂₃₃
                have h₂₃₈ : (q : ℝ) < (p : ℝ) := by linarith
                have h₂₃₉ : (q : ℝ) < Real.sqrt (2 * Y / (p : ℝ)) := by linarith
                rw [min_lt_iff]
                exact ⟨h₂₃₈, h₂₃₉⟩
              exact h₂₃₄
            exact ⟨h₂₀, h₂₁, h₂₂, h₂₃⟩
          · -- Case i = 42
            have h₉ : i' = 42 := by linarith
            have h₁₀ : (Y : ℝ) ^ (regionData 42 0 : ℝ) < (p : ℝ) := hp₁
            have h₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (regionData 42 1 : ℝ) := hp₂
            have h₁₂ : (p : ℝ) ^ (regionData 42 2 : ℝ) * (Y : ℝ) ^ (regionData 42 3 : ℝ) < (q : ℝ) := hq₁
            have h₁₃ : (q : ℝ) < (p : ℝ) ^ (regionData 42 4 : ℝ) * (Y : ℝ) ^ (regionData 42 5 : ℝ) := hq₂
            have h₁₄ : (regionData 42 0 : ℝ) = (1823 / 4725 : ℝ) := by norm_num [regionData]
            have h₁₅ : (regionData 42 1 : ℝ) = (3041 / 7830 : ℝ) := by norm_num [regionData]
            have h₁₆ : (regionData 42 2 : ℝ) = (0 : ℝ) := by norm_num [regionData]
            have h₁₇ : (regionData 42 3 : ℝ) = (16 / 135 : ℝ) := by norm_num [regionData]
            have h₁₈ : (regionData 42 4 : ℝ) = (-58 / 49 : ℝ) := by norm_num [regionData]
            have h₁₉ : (regionData 42 5 : ℝ) = (85 / 147 : ℝ) := by norm_num [regionData]
            rw [h₁₄] at h₁₀
            rw [h₁₅] at h₁₁
            rw [h₁₆, h₁₇] at h₁₂
            rw [h₁₈, h₁₉] at h₁₃
            have h₂₀ : (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) := by
              have h₂₀₁ : (Y : ℝ) ^ (16 / 135 : ℝ) < (Y : ℝ) ^ (1823 / 4725 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₁ : (p : ℝ) ≤ Real.sqrt (2 * Y) := by
              have h₂₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (3041 / 7830 : ℝ) := h₁₁
              have h₂₁₂ : (Y : ℝ) ^ (3041 / 7830 : ℝ) ≤ Real.sqrt (2 * Y) := by
                have h₂₁₃ : (Y : ℝ) ^ (3041 / 7830 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                have h₂₁₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                  rw [Real.sqrt_eq_rpow]
                  <;> norm_num
                rw [h₂₁₄] at h₂₁₃
                have h₂₁₅ : Real.sqrt Y ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt (by positivity)
                linarith
              linarith
            have h₂₂ : (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) := by
              have h₂₂₁ : (q : ℝ) > (p : ℝ) ^ (0 : ℝ) * (Y : ℝ) ^ (16 / 135 : ℝ) := by
                calc
                  (q : ℝ) > (p : ℝ) ^ (0 : ℝ) * (Y : ℝ) ^ (16 / 135 : ℝ) := by
                    simpa [h₁₆, h₁₇] using h₁₂
                  _ = (p : ℝ) ^ (0 : ℝ) * (Y : ℝ) ^ (16 / 135 : ℝ) := by rfl
              have h₂₂₂ : (p : ℝ) ^ (0 : ℝ) * (Y : ℝ) ^ (16 / 135 : ℝ) = (Y : ℝ) ^ (16 / 135 : ℝ) := by
                have h₂₂₃ : (p : ℝ) ^ (0 : ℝ) = 1 := by
                  norm_cast
                  <;> simp [hp.ne_zero]
                rw [h₂₂₃]
                <;> ring_nf
                <;> field_simp
              have h₂₂₃ : (q : ℝ) > (Y : ℝ) ^ (16 / 135 : ℝ) := by linarith
              linarith
            have h₂₃ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
              have h₂₃₁ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
              have h₂₃₂ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                have h₂₃₃ : (p : ℝ) ≥ (Y : ℝ) ^ (1823 / 4725 : ℝ) := by linarith
                have h₂₃₄ : 0 < (p : ℝ) := by positivity
                have h₂₃₅ : 0 < (Y : ℝ) := by positivity
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := by
                  have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₇]
                  have h₂₃₈ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (p : ℝ) := by
                    have h₂₃₉ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ (p : ℝ) ^ (58 / 49 : ℝ) := le_refl _
                    have h₂₄₀ : (p : ℝ) ≥ (Y : ℝ) ^ (1823 / 4725 : ℝ) := by linarith
                    have h₂₄₁ : (p : ℝ) ^ (58 / 49 : ℝ) ≥ ((Y : ℝ) ^ (1823 / 4725 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (1823 / 4725 : ℝ)) ^ (58 / 49 : ℝ) := by
                      apply div_le_div_of_le_left (by positivity) (by positivity)
                      exact h₂₄₁
                    have h₂₄₃ : (Y : ℝ) ^ (85 / 147 : ℝ) / ((Y : ℝ) ^ (1823 / 4725 : ℝ)) ^ (58 / 49 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((1823 / 4725 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_mul (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₃] at h₂₄₂
                    have h₂₄₄ : (Y : ℝ) ^ (85 / 147 : ℝ) / (Y : ℝ) ^ ((1823 / 4725 : ℝ) * (58 / 49 : ℝ)) = (Y : ℝ) ^ ((85 / 147 : ℝ) - (1823 / 4725 : ℝ) * (58 / 49 : ℝ)) := by
                      rw [← Real.rpow_sub (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₄] at h₂₄₂
                    have h₂₄₅ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (1823 / 4725 : ℝ) * (58 / 49 : ℝ)) ≤ (p : ℝ) := by
                      have h₂₄₆ : (85 / 147 : ℝ) - (1823 / 4725 : ℝ) * (58 / 49 : ℝ) < (1823 / 4725 : ℝ) := by norm_num
                      have h₂₄₇ : (Y : ℝ) ^ ((85 / 147 : ℝ) - (1823 / 4725 : ℝ) * (58 / 49 : ℝ)) < (Y : ℝ) ^ (1823 / 4725 : ℝ) := by
                        apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₄₆ ⊢ <;> linarith)
                      have h₂₄₈ : (Y : ℝ) ^ (1823 / 4725 : ℝ) ≤ (p : ℝ) := by linarith
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₃ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                have h₂₃₄ : (p : ℝ) ≤ (Y : ℝ) ^ (3041 / 7830 : ℝ) := h₁₁
                have h₂₃₅ : 0 < (p : ℝ) := by positivity
                have h₂₃₆ : 0 < (Y : ℝ) := by positivity
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                  have h₂₃₈ : Real.sqrt (2 * Y / (p : ℝ)) = Real.sqrt (2 * Y / (p : ℝ)) := rfl
                  have h₂₃₉ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) = (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₉]
                  have h₂₄₀ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                    have h₂₄₁ : Real.sqrt (2 * Y / (p : ℝ)) ≥ 0 := Real.sqrt_nonneg _
                    have h₂₄₂ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≥ 0 := by positivity
                    have h₂₄₃ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 ≤ (2 * Y / (p : ℝ)) := by
                      have h₂₄₄ : ((Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ)) ^ 2 = (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) := by
                        field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                        <;> field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                      rw [h₂₄₄]
                      have h₂₄₅ : (p : ℝ) ≥ (Y : ℝ) ^ (1823 / 4725 : ℝ) := by linarith
                      have h₂₄₆ : (p : ℝ) ≤ (Y : ℝ) ^ (3041 / 7830 : ℝ) := h₁₁
                      have h₂₄₇ : (Y : ℝ) ^ (170 / 147 : ℝ) / (p : ℝ) ^ (116 / 49 : ℝ) ≤ (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (1823 / 4725 : ℝ)) ^ (116 / 49 : ℝ) := by
                        apply div_le_div_of_le_left (by positivity) (by positivity)
                        have h₂₄₈ : (p : ℝ) ^ (116 / 49 : ℝ) ≥ ((Y : ℝ) ^ (1823 / 4725 : ℝ)) ^ (116 / 49 : ℝ) := by
                          apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                        linarith
                      have h₂₄₉ : (Y : ℝ) ^ (170 / 147 : ℝ) / ((Y : ℝ) ^ (1823 / 4725 : ℝ)) ^ (116 / 49 : ℝ) = (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((1823 / 4725 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_mul (by positivity)]
                        <;> ring_nf
                      rw [h₂₄₉] at h₂₄₇
                      have h₂₅₀ : (Y : ℝ) ^ (170 / 147 : ℝ) / (Y : ℝ) ^ ((1823 / 4725 : ℝ) * (116 / 49 : ℝ)) = (Y : ℝ) ^ ((170 / 147 : ℝ) - (1823 / 4725 : ℝ) * (116 / 49 : ℝ)) := by
                        rw [← Real.rpow_sub (by positivity)]
                        <;> ring_nf
                      rw [h₂₅₀] at h₂₄₇
                      have h₂₅₁ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (1823 / 4725 : ℝ) * (116 / 49 : ℝ)) ≤ 2 * Y / (p : ℝ) := by
                        have h₂₅₂ : (170 / 147 : ℝ) - (1823 / 4725 : ℝ) * (116 / 49 : ℝ) < (1 / 2 : ℝ) := by norm_num
                        have h₂₅₃ : (Y : ℝ) ^ ((170 / 147 : ℝ) - (1823 / 4725 : ℝ) * (116 / 49 : ℝ)) < (Y : ℝ) ^ (1 / 2 : ℝ) := by
                          apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₅₂ ⊢ <;> linarith)
                        have h₂₅₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                          rw [Real.sqrt_eq_rpow]
                          <;> norm_num
                        rw [h₂₅₄] at h₂₅₃
                        have h₂₅₅ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                          have h₂₅₆ : (p : ℝ) ≤ (Y : ℝ) ^ (3041 / 7830 : ℝ) := h₁₁
                          have h₂₅₇ : (Y : ℝ) ^ (3041 / 7830 : ℝ) ≤ (Y : ℝ) := by
                            apply Real.rpow_le_rpow (by linarith) (by norm_num)
                          have h₂₅₈ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                          have h₂₅₉ : 0 < (p : ℝ) := by positivity
                          have h₂₆₀ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                            have h₂₆₁ : Real.sqrt Y = (Y : ℝ) ^ (1 / 2 : ℝ) := by
                              rw [Real.sqrt_eq_rpow]
                              <;> norm_num
                            rw [h₂₆₁]
                            have h₂₆₂ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * Y / (p : ℝ) := by
                              have h₂₆₃ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                              have h₂₆₄ : 0 < (p : ℝ) := by positivity
                              have h₂₆₅ : 2 * Y / (p : ℝ) ≥ 2 * Y / (Y : ℝ) := by
                                apply div_le_div_of_le_left (by positivity) (by positivity)
                                linarith
                              have h₂₆₆ : 2 * Y / (Y : ℝ) = 2 := by
                                field_simp [h₂₃₆.ne']
                                <;> ring_nf
                              have h₂₆₇ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
                                have h₂₆₈ : (Y : ℝ) ≥ 1000000 := by exact_mod_cast h₁
                                have h₂₆₉ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ (Y : ℝ) := by
                                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                                have h₂₇₀ : (Y : ℝ) ≤ 2 * (Y : ℝ) := by linarith
                                nlinarith [Real.sqrt_nonneg (Y : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (Y : ℝ))]
                              linarith
                            linarith
                          linarith
                        linarith
                      linarith
                    have h₂₄₅ : (Y : ℝ) ^ (85 / 147 : ℝ) / (p : ℝ) ^ (58 / 49 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                      apply Real.le_sqrt_of_sq_le
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₄ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
                have h₂₃₅ : (q : ℝ) < (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) := by linarith
                have h₂₃₆ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ (p : ℝ) := h₂₃₂
                have h₂₃₇ : (p : ℝ) ^ (-58 / 49 : ℝ) * (Y : ℝ) ^ (85 / 147 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := h₂₃₃
                have h₂₃₈ : (q : ℝ) < (p : ℝ) := by linarith
                have h₂₃₉ : (q : ℝ) < Real.sqrt (2 * Y / (p : ℝ)) := by linarith
                rw [min_lt_iff]
                exact ⟨h₂₃₈, h₂₃₉⟩
              exact h₂₃₄
            exact ⟨h₂₀, h₂₁, h₂₂, h₂₃⟩
          · -- Case i = 46
            have h₉ : i' = 46 := by linarith
            have h₁₀ : (Y : ℝ) ^ (regionData 46 0 : ℝ) < (p : ℝ) := hp₁
            have h₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (regionData 46 1 : ℝ) := hp₂
            have h₁₂ : (p : ℝ) ^ (regionData 46 2 : ℝ) * (Y : ℝ) ^ (regionData 46 3 : ℝ) < (q : ℝ) := hq₁
            have h₁₃ : (q : ℝ) < (p : ℝ) ^ (regionData 46 4 : ℝ) * (Y : ℝ) ^ (regionData 46 5 : ℝ) := hq₂
            have h₁₄ : (regionData 46 0 : ℝ) = (11 / 27 : ℝ) := by norm_num [regionData]
            have h₁₅ : (regionData 46 1 : ℝ) = (34 / 81 : ℝ) := by norm_num [regionData]
            have h₁₆ : (regionData 46 2 : ℝ) = (-29 / 19 : ℝ) := by norm_num [regionData]
            have h₁₇ : (regionData 46 3 : ℝ) = (89 / 114 : ℝ) := by norm_num [regionData]
            have h₁₈ : (regionData 46 4 : ℝ) = (-35 / 23 : ℝ) := by norm_num [regionData]
            have h₁₉ : (regionData 46 5 : ℝ) = (18 / 23 : ℝ) := by norm_num [regionData]
            rw [h₁₄] at h₁₀
            rw [h₁₅] at h₁₁
            rw [h₁₆, h₁₇] at h₁₂
            rw [h₁₈, h₁₉] at h₁₃
            have h₂₀ : (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) := by
              have h₂₀₁ : (Y : ℝ) ^ (16 / 135 : ℝ) < (Y : ℝ) ^ (11 / 27 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₁ : (p : ℝ) ≤ Real.sqrt (2 * Y) := by
              have h₂₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (34 / 81 : ℝ) := h₁₁
              have h₂₁₂ : (Y : ℝ) ^ (34 / 81 : ℝ) ≤ Real.sqrt (2 * Y) := by
                have h₂₁₃ : (Y : ℝ) ^ (34 / 81 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                have h₂₁₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                  rw [Real.sqrt_eq_rpow]
                  <;> norm_num
                rw [h₂₁₄] at h₂₁₃
                have h₂₁₅ : Real.sqrt Y ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt (by positivity)
                linarith
              linarith
            have h₂₂ : (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) := by
              have h₂₂₁ : (q : ℝ) > (p : ℝ) ^ (-29 / 19 : ℝ) * (Y : ℝ) ^ (89 / 114 : ℝ) := by linarith
              have h₂₂₂ : (p : ℝ) ^ (-29 / 19 : ℝ) * (Y : ℝ) ^ (89 / 114 : ℝ) ≥ (Y : ℝ) ^ ((34 / 81 : ℝ) * (-29 / 19 : ℝ) + (89 / 114 : ℝ)) := by
                have h₂₂₃ : (p : ℝ) ≤ (Y : ℝ) ^ (34 / 81 : ℝ) := h₁₁
                have h₂₂₄ : 0 < (p : ℝ) := by positivity
                have h₂₂₅ : 0 < (Y : ℝ) := by positivity
                have h₂₂₆ : (p : ℝ) ^ (-29 / 19 : ℝ) ≥ ((Y : ℝ) ^ (34 / 81 : ℝ)) ^ (-29 / 19 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by linarith) (by norm_num)
                calc
                  (p : ℝ) ^ (-29 / 19 : ℝ) * (Y : ℝ) ^ (89 / 114 : ℝ) ≥ ((Y : ℝ) ^ (34 / 81 : ℝ)) ^ (-29 / 19 : ℝ) * (Y : ℝ) ^ (89 / 114 : ℝ) := by gcongr
                  _ = (Y : ℝ) ^ ((34 / 81 : ℝ) * (-29 / 19 : ℝ)) * (Y : ℝ) ^ (89 / 114 : ℝ) := by
                    rw [← Real.rpow_mul (by positivity)]
                    <;> ring_nf
                  _ = (Y : ℝ) ^ ((34 / 81 : ℝ) * (-29 / 19 : ℝ) + (89 / 114 : ℝ)) := by
                    rw [← Real.rpow_add (by positivity)]
                    <;> ring_nf
              have h₂₂₇ : (Y : ℝ) ^ ((34 / 81 : ℝ) * (-29 / 19 : ℝ) + (89 / 114 : ℝ)) > (Y : ℝ) ^ (16 / 135 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₃ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
              have h₂₃₁ : (q : ℝ) < (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) := by linarith
              have h₂₃₂ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ (p : ℝ) := by
                have h₂₃₃ : (p : ℝ) ≥ (Y : ℝ) ^ (11 / 27 : ℝ) := by linarith
                have h₂₃₄ : 0 < (p : ℝ) := by positivity
                have h₂₃₅ : 0 < (Y : ℝ) := by positivity
                have h₂₃₆ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ (p : ℝ) := by
                  have h₂₃₇ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) = (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₇]
                  have h₂₃₈ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≤ (p : ℝ) := by
                    have h₂₃₉ : (p : ℝ) ^ (35 / 23 : ℝ) ≥ (p : ℝ) ^ (35 / 23 : ℝ) := le_refl _
                    have h₂₄₀ : (p : ℝ) ≥ (Y : ℝ) ^ (11 / 27 : ℝ) := by linarith
                    have h₂₄₁ : (p : ℝ) ^ (35 / 23 : ℝ) ≥ ((Y : ℝ) ^ (11 / 27 : ℝ)) ^ (35 / 23 : ℝ) := by
                      apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                    have h₂₄₂ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≤ (Y : ℝ) ^ (18 / 23 : ℝ) / ((Y : ℝ) ^ (11 / 27 : ℝ)) ^ (35 / 23 : ℝ) := by
                      apply div_le_div_of_le_left (by positivity) (by positivity)
                      exact h₂₄₁
                    have h₂₄₃ : (Y : ℝ) ^ (18 / 23 : ℝ) / ((Y : ℝ) ^ (11 / 27 : ℝ)) ^ (35 / 23 : ℝ) = (Y : ℝ) ^ (18 / 23 : ℝ) / (Y : ℝ) ^ ((11 / 27 : ℝ) * (35 / 23 : ℝ)) := by
                      rw [← Real.rpow_mul (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₃] at h₂₄₂
                    have h₂₄₄ : (Y : ℝ) ^ (18 / 23 : ℝ) / (Y : ℝ) ^ ((11 / 27 : ℝ) * (35 / 23 : ℝ)) = (Y : ℝ) ^ ((18 / 23 : ℝ) - (11 / 27 : ℝ) * (35 / 23 : ℝ)) := by
                      rw [← Real.rpow_sub (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₄] at h₂₄₂
                    have h₂₄₅ : (Y : ℝ) ^ ((18 / 23 : ℝ) - (11 / 27 : ℝ) * (35 / 23 : ℝ)) ≤ (p : ℝ) := by
                      have h₂₄₆ : (18 / 23 : ℝ) - (11 / 27 : ℝ) * (35 / 23 : ℝ) < (11 / 27 : ℝ) := by norm_num
                      have h₂₄₇ : (Y : ℝ) ^ ((18 / 23 : ℝ) - (11 / 27 : ℝ) * (35 / 23 : ℝ)) < (Y : ℝ) ^ (11 / 27 : ℝ) := by
                        apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₄₆ ⊢ <;> linarith)
                      have h₂₄₈ : (Y : ℝ) ^ (11 / 27 : ℝ) ≤ (p : ℝ) := by linarith
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₃ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                have h₂₃₄ : (p : ℝ) ≤ (Y : ℝ) ^ (34 / 81 : ℝ) := h₁₁
                have h₂₃₅ : 0 < (p : ℝ) := by positivity
                have h₂₃₆ : 0 < (Y : ℝ) := by positivity
                have h₂₃₇ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                  have h₂₃₈ : Real.sqrt (2 * Y / (p : ℝ)) = Real.sqrt (2 * Y / (p : ℝ)) := rfl
                  have h₂₃₉ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) = (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₉]
                  have h₂₄₀ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                    have h₂₄₁ : Real.sqrt (2 * Y / (p : ℝ)) ≥ 0 := Real.sqrt_nonneg _
                    have h₂₄₂ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≥ 0 := by positivity
                    have h₂₄₃ : ((Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ)) ^ 2 ≤ (2 * Y / (p : ℝ)) := by
                      have h₂₄₄ : ((Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ)) ^ 2 = (Y : ℝ) ^ (36 / 23 : ℝ) / (p : ℝ) ^ (70 / 23 : ℝ) := by
                        field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                        <;> field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                      rw [h₂₄₄]
                      have h₂₄₅ : (p : ℝ) ≥ (Y : ℝ) ^ (11 / 27 : ℝ) := by linarith
                      have h₂₄₆ : (p : ℝ) ≤ (Y : ℝ) ^ (34 / 81 : ℝ) := h₁₁
                      have h₂₄₇ : (Y : ℝ) ^ (36 / 23 : ℝ) / (p : ℝ) ^ (70 / 23 : ℝ) ≤ (Y : ℝ) ^ (36 / 23 : ℝ) / ((Y : ℝ) ^ (11 / 27 : ℝ)) ^ (70 / 23 : ℝ) := by
                        apply div_le_div_of_le_left (by positivity) (by positivity)
                        have h₂₄₈ : (p : ℝ) ^ (70 / 23 : ℝ) ≥ ((Y : ℝ) ^ (11 / 27 : ℝ)) ^ (70 / 23 : ℝ) := by
                          apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                        linarith
                      have h₂₄₉ : (Y : ℝ) ^ (36 / 23 : ℝ) / ((Y : ℝ) ^ (11 / 27 : ℝ)) ^ (70 / 23 : ℝ) = (Y : ℝ) ^ (36 / 23 : ℝ) / (Y : ℝ) ^ ((11 / 27 : ℝ) * (70 / 23 : ℝ)) := by
                        rw [← Real.rpow_mul (by positivity)]
                        <;> ring_nf
                      rw [h₂₄₉] at h₂₄₇
                      have h₂₅₀ : (Y : ℝ) ^ (36 / 23 : ℝ) / (Y : ℝ) ^ ((11 / 27 : ℝ) * (70 / 23 : ℝ)) = (Y : ℝ) ^ ((36 / 23 : ℝ) - (11 / 27 : ℝ) * (70 / 23 : ℝ)) := by
                        rw [← Real.rpow_sub (by positivity)]
                        <;> ring_nf
                      rw [h₂₅₀] at h₂₄₇
                      have h₂₅₁ : (Y : ℝ) ^ ((36 / 23 : ℝ) - (11 / 27 : ℝ) * (70 / 23 : ℝ)) ≤ 2 * Y / (p : ℝ) := by
                        have h₂₅₂ : (36 / 23 : ℝ) - (11 / 27 : ℝ) * (70 / 23 : ℝ) < (1 / 2 : ℝ) := by norm_num
                        have h₂₅₃ : (Y : ℝ) ^ ((36 / 23 : ℝ) - (11 / 27 : ℝ) * (70 / 23 : ℝ)) < (Y : ℝ) ^ (1 / 2 : ℝ) := by
                          apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₅₂ ⊢ <;> linarith)
                        have h₂₅₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                          rw [Real.sqrt_eq_rpow]
                          <;> norm_num
                        rw [h₂₅₄] at h₂₅₃
                        have h₂₅₅ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                          have h₂₅₆ : (p : ℝ) ≤ (Y : ℝ) ^ (34 / 81 : ℝ) := h₁₁
                          have h₂₅₇ : (Y : ℝ) ^ (34 / 81 : ℝ) ≤ (Y : ℝ) := by
                            apply Real.rpow_le_rpow (by linarith) (by norm_num)
                          have h₂₅₈ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                          have h₂₅₉ : 0 < (p : ℝ) := by positivity
                          have h₂₆₀ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                            have h₂₆₁ : Real.sqrt Y = (Y : ℝ) ^ (1 / 2 : ℝ) := by
                              rw [Real.sqrt_eq_rpow]
                              <;> norm_num
                            rw [h₂₆₁]
                            have h₂₆₂ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * Y / (p : ℝ) := by
                              have h₂₆₃ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                              have h₂₆₄ : 0 < (p : ℝ) := by positivity
                              have h₂₆₅ : 2 * Y / (p : ℝ) ≥ 2 * Y / (Y : ℝ) := by
                                apply div_le_div_of_le_left (by positivity) (by positivity)
                                linarith
                              have h₂₆₆ : 2 * Y / (Y : ℝ) = 2 := by
                                field_simp [h₂₃₆.ne']
                                <;> ring_nf
                              have h₂₆₇ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
                                have h₂₆₈ : (Y : ℝ) ≥ 1000000 := by exact_mod_cast h₁
                                have h₂₆₉ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ (Y : ℝ) := by
                                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                                have h₂₇₀ : (Y : ℝ) ≤ 2 * (Y : ℝ) := by linarith
                                nlinarith [Real.sqrt_nonneg (Y : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (Y : ℝ))]
                              linarith
                            linarith
                          linarith
                        linarith
                      linarith
                    have h₂₄₅ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                      apply Real.le_sqrt_of_sq_le
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₄ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
                have h₂₃₅ : (q : ℝ) < (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) := by linarith
                have h₂₃₆ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ (p : ℝ) := h₂₃₂
                have h₂₃₇ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := h₂₃₃
                have h₂₃₈ : (q : ℝ) < (p : ℝ) := by linarith
                have h₂₃₉ : (q : ℝ) < Real.sqrt (2 * Y / (p : ℝ)) := by linarith
                rw [min_lt_iff]
                exact ⟨h₂₃₈, h₂₃₉⟩
              exact h₂₃₄
            exact ⟨h₂₀, h₂₁, h₂₂, h₂₃⟩
          · -- Case i = 49
            have h₉ : i' = 49 := by linarith
            have h₁₀ : (Y : ℝ) ^ (regionData 49 0 : ℝ) < (p : ℝ) := hp₁
            have h₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (regionData 49 1 : ℝ) := hp₂
            have h₁₂ : (p : ℝ) ^ (regionData 49 2 : ℝ) * (Y : ℝ) ^ (regionData 49 3 : ℝ) < (q : ℝ) := hq₁
            have h₁₃ : (q : ℝ) < (p : ℝ) ^ (regionData 49 4 : ℝ) * (Y : ℝ) ^ (regionData 49 5 : ℝ) := hq₂
            have h₁₄ : (regionData 49 0 : ℝ) = (34 / 81 : ℝ) := by norm_num [regionData]
            have h₁₅ : (regionData 49 1 : ℝ) = (49 / 114 : ℝ) := by norm_num [regionData]
            have h₁₆ : (regionData 49 2 : ℝ) = (-29 / 19 : ℝ) := by norm_num [regionData]
            have h₁₇ : (regionData 49 3 : ℝ) = (89 / 114 : ℝ) := by norm_num [regionData]
            have h₁₈ : (regionData 49 4 : ℝ) = (-35 / 23 : ℝ) := by norm_num [regionData]
            have h₁₉ : (regionData 49 5 : ℝ) = (18 / 23 : ℝ) := by norm_num [regionData]
            rw [h₁₄] at h₁₀
            rw [h₁₅] at h₁₁
            rw [h₁₆, h₁₇] at h₁₂
            rw [h₁₈, h₁₉] at h₁₃
            have h₂₀ : (Y : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) := by
              have h₂₀₁ : (Y : ℝ) ^ (16 / 135 : ℝ) < (Y : ℝ) ^ (34 / 81 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₁ : (p : ℝ) ≤ Real.sqrt (2 * Y) := by
              have h₂₁₁ : (p : ℝ) ≤ (Y : ℝ) ^ (49 / 114 : ℝ) := h₁₁
              have h₂₁₂ : (Y : ℝ) ^ (49 / 114 : ℝ) ≤ Real.sqrt (2 * Y) := by
                have h₂₁₃ : (Y : ℝ) ^ (49 / 114 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                have h₂₁₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                  rw [Real.sqrt_eq_rpow]
                  <;> norm_num
                rw [h₂₁₄] at h₂₁₃
                have h₂₁₅ : Real.sqrt Y ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt (by positivity)
                linarith
              linarith
            have h₂₂ : (Y : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) := by
              have h₂₂₁ : (q : ℝ) > (p : ℝ) ^ (-29 / 19 : ℝ) * (Y : ℝ) ^ (89 / 114 : ℝ) := by linarith
              have h₂₂₂ : (p : ℝ) ^ (-29 / 19 : ℝ) * (Y : ℝ) ^ (89 / 114 : ℝ) ≥ (Y : ℝ) ^ ((49 / 114 : ℝ) * (-29 / 19 : ℝ) + (89 / 114 : ℝ)) := by
                have h₂₂₃ : (p : ℝ) ≤ (Y : ℝ) ^ (49 / 114 : ℝ) := h₁₁
                have h₂₂₄ : 0 < (p : ℝ) := by positivity
                have h₂₂₅ : 0 < (Y : ℝ) := by positivity
                have h₂₂₆ : (p : ℝ) ^ (-29 / 19 : ℝ) ≥ ((Y : ℝ) ^ (49 / 114 : ℝ)) ^ (-29 / 19 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by linarith) (by norm_num)
                calc
                  (p : ℝ) ^ (-29 / 19 : ℝ) * (Y : ℝ) ^ (89 / 114 : ℝ) ≥ ((Y : ℝ) ^ (49 / 114 : ℝ)) ^ (-29 / 19 : ℝ) * (Y : ℝ) ^ (89 / 114 : ℝ) := by gcongr
                  _ = (Y : ℝ) ^ ((49 / 114 : ℝ) * (-29 / 19 : ℝ)) * (Y : ℝ) ^ (89 / 114 : ℝ) := by
                    rw [← Real.rpow_mul (by positivity)]
                    <;> ring_nf
                  _ = (Y : ℝ) ^ ((49 / 114 : ℝ) * (-29 / 19 : ℝ) + (89 / 114 : ℝ)) := by
                    rw [← Real.rpow_add (by positivity)]
                    <;> ring_nf
              have h₂₂₇ : (Y : ℝ) ^ ((49 / 114 : ℝ) * (-29 / 19 : ℝ) + (89 / 114 : ℝ)) > (Y : ℝ) ^ (16 / 135 : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by norm_num)
              linarith
            have h₂₃ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
              have h₂₃₁ : (q : ℝ) < (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) := by linarith
              have h₂₃₂ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ (p : ℝ) := by
                have h₂₃₃ : (p : ℝ) ≥ (Y : ℝ) ^ (34 / 81 : ℝ) := by linarith
                have h₂₃₄ : 0 < (p : ℝ) := by positivity
                have h₂₃₅ : 0 < (Y : ℝ) := by positivity
                have h₂₃₆ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ (p : ℝ) := by
                  have h₂₃₇ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) = (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₇]
                  have h₂₃₈ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≤ (p : ℝ) := by
                    have h₂₃₉ : (p : ℝ) ^ (35 / 23 : ℝ) ≥ (p : ℝ) ^ (35 / 23 : ℝ) := le_refl _
                    have h₂₄₀ : (p : ℝ) ≥ (Y : ℝ) ^ (34 / 81 : ℝ) := by linarith
                    have h₂₄₁ : (p : ℝ) ^ (35 / 23 : ℝ) ≥ ((Y : ℝ) ^ (34 / 81 : ℝ)) ^ (35 / 23 : ℝ) := by
                      apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                    have h₂₄₂ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≤ (Y : ℝ) ^ (18 / 23 : ℝ) / ((Y : ℝ) ^ (34 / 81 : ℝ)) ^ (35 / 23 : ℝ) := by
                      apply div_le_div_of_le_left (by positivity) (by positivity)
                      exact h₂₄₁
                    have h₂₄₃ : (Y : ℝ) ^ (18 / 23 : ℝ) / ((Y : ℝ) ^ (34 / 81 : ℝ)) ^ (35 / 23 : ℝ) = (Y : ℝ) ^ (18 / 23 : ℝ) / (Y : ℝ) ^ ((34 / 81 : ℝ) * (35 / 23 : ℝ)) := by
                      rw [← Real.rpow_mul (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₃] at h₂₄₂
                    have h₂₄₄ : (Y : ℝ) ^ (18 / 23 : ℝ) / (Y : ℝ) ^ ((34 / 81 : ℝ) * (35 / 23 : ℝ)) = (Y : ℝ) ^ ((18 / 23 : ℝ) - (34 / 81 : ℝ) * (35 / 23 : ℝ)) := by
                      rw [← Real.rpow_sub (by positivity)]
                      <;> ring_nf
                    rw [h₂₄₄] at h₂₄₂
                    have h₂₄₅ : (Y : ℝ) ^ ((18 / 23 : ℝ) - (34 / 81 : ℝ) * (35 / 23 : ℝ)) ≤ (p : ℝ) := by
                      have h₂₄₆ : (18 / 23 : ℝ) - (34 / 81 : ℝ) * (35 / 23 : ℝ) < (34 / 81 : ℝ) := by norm_num
                      have h₂₄₇ : (Y : ℝ) ^ ((18 / 23 : ℝ) - (34 / 81 : ℝ) * (35 / 23 : ℝ)) < (Y : ℝ) ^ (34 / 81 : ℝ) := by
                        apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₄₆ ⊢ <;> linarith)
                      have h₂₄₈ : (Y : ℝ) ^ (34 / 81 : ℝ) ≤ (p : ℝ) := by linarith
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₃ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                have h₂₃₄ : (p : ℝ) ≤ (Y : ℝ) ^ (49 / 114 : ℝ) := h₁₁
                have h₂₃₅ : 0 < (p : ℝ) := by positivity
                have h₂₃₆ : 0 < (Y : ℝ) := by positivity
                have h₂₃₇ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                  have h₂₃₈ : Real.sqrt (2 * Y / (p : ℝ)) = Real.sqrt (2 * Y / (p : ℝ)) := rfl
                  have h₂₃₉ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) = (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) := by
                    field_simp [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_sub (by positivity)]
                    <;> ring_nf
                    <;> field_simp [Real.rpow_neg (by positivity)]
                    <;> ring_nf
                  rw [h₂₃₉]
                  have h₂₄₀ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                    have h₂₄₁ : Real.sqrt (2 * Y / (p : ℝ)) ≥ 0 := Real.sqrt_nonneg _
                    have h₂₄₂ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≥ 0 := by positivity
                    have h₂₄₃ : ((Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ)) ^ 2 ≤ (2 * Y / (p : ℝ)) := by
                      have h₂₄₄ : ((Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ)) ^ 2 = (Y : ℝ) ^ (36 / 23 : ℝ) / (p : ℝ) ^ (70 / 23 : ℝ) := by
                        field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                        <;> field_simp [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_nat_cast]
                        <;> ring_nf
                      rw [h₂₄₄]
                      have h₂₄₅ : (p : ℝ) ≥ (Y : ℝ) ^ (34 / 81 : ℝ) := by linarith
                      have h₂₄₆ : (p : ℝ) ≤ (Y : ℝ) ^ (49 / 114 : ℝ) := h₁₁
                      have h₂₄₇ : (Y : ℝ) ^ (36 / 23 : ℝ) / (p : ℝ) ^ (70 / 23 : ℝ) ≤ (Y : ℝ) ^ (36 / 23 : ℝ) / ((Y : ℝ) ^ (34 / 81 : ℝ)) ^ (70 / 23 : ℝ) := by
                        apply div_le_div_of_le_left (by positivity) (by positivity)
                        have h₂₄₈ : (p : ℝ) ^ (70 / 23 : ℝ) ≥ ((Y : ℝ) ^ (34 / 81 : ℝ)) ^ (70 / 23 : ℝ) := by
                          apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
                        linarith
                      have h₂₄₉ : (Y : ℝ) ^ (36 / 23 : ℝ) / ((Y : ℝ) ^ (34 / 81 : ℝ)) ^ (70 / 23 : ℝ) = (Y : ℝ) ^ (36 / 23 : ℝ) / (Y : ℝ) ^ ((34 / 81 : ℝ) * (70 / 23 : ℝ)) := by
                        rw [← Real.rpow_mul (by positivity)]
                        <;> ring_nf
                      rw [h₂₄₉] at h₂₄₇
                      have h₂₅₀ : (Y : ℝ) ^ (36 / 23 : ℝ) / (Y : ℝ) ^ ((34 / 81 : ℝ) * (70 / 23 : ℝ)) = (Y : ℝ) ^ ((36 / 23 : ℝ) - (34 / 81 : ℝ) * (70 / 23 : ℝ)) := by
                        rw [← Real.rpow_sub (by positivity)]
                        <;> ring_nf
                      rw [h₂₅₀] at h₂₄₇
                      have h₂₅₁ : (Y : ℝ) ^ ((36 / 23 : ℝ) - (34 / 81 : ℝ) * (70 / 23 : ℝ)) ≤ 2 * Y / (p : ℝ) := by
                        have h₂₅₂ : (36 / 23 : ℝ) - (34 / 81 : ℝ) * (70 / 23 : ℝ) < (1 / 2 : ℝ) := by norm_num
                        have h₂₅₃ : (Y : ℝ) ^ ((36 / 23 : ℝ) - (34 / 81 : ℝ) * (70 / 23 : ℝ)) < (Y : ℝ) ^ (1 / 2 : ℝ) := by
                          apply Real.rpow_lt_rpow (by linarith) (by norm_num at h₂₅₂ ⊢ <;> linarith)
                        have h₂₅₄ : (Y : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt Y := by
                          rw [Real.sqrt_eq_rpow]
                          <;> norm_num
                        rw [h₂₅₄] at h₂₅₃
                        have h₂₅₅ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                          have h₂₅₆ : (p : ℝ) ≤ (Y : ℝ) ^ (49 / 114 : ℝ) := h₁₁
                          have h₂₅₇ : (Y : ℝ) ^ (49 / 114 : ℝ) ≤ (Y : ℝ) := by
                            apply Real.rpow_le_rpow (by linarith) (by norm_num)
                          have h₂₅₈ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                          have h₂₅₉ : 0 < (p : ℝ) := by positivity
                          have h₂₆₀ : Real.sqrt Y ≤ 2 * Y / (p : ℝ) := by
                            have h₂₆₁ : Real.sqrt Y = (Y : ℝ) ^ (1 / 2 : ℝ) := by
                              rw [Real.sqrt_eq_rpow]
                              <;> norm_num
                            rw [h₂₆₁]
                            have h₂₆₂ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * Y / (p : ℝ) := by
                              have h₂₆₃ : (p : ℝ) ≤ (Y : ℝ) := by linarith
                              have h₂₆₄ : 0 < (p : ℝ) := by positivity
                              have h₂₆₅ : 2 * Y / (p : ℝ) ≥ 2 * Y / (Y : ℝ) := by
                                apply div_le_div_of_le_left (by positivity) (by positivity)
                                linarith
                              have h₂₆₆ : 2 * Y / (Y : ℝ) = 2 := by
                                field_simp [h₂₃₆.ne']
                                <;> ring_nf
                              have h₂₆₇ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
                                have h₂₆₈ : (Y : ℝ) ≥ 1000000 := by exact_mod_cast h₁
                                have h₂₆₉ : (Y : ℝ) ^ (1 / 2 : ℝ) ≤ (Y : ℝ) := by
                                  apply Real.rpow_le_rpow (by linarith) (by norm_num)
                                have h₂₇₀ : (Y : ℝ) ≤ 2 * (Y : ℝ) := by linarith
                                nlinarith [Real.sqrt_nonneg (Y : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (Y : ℝ))]
                              linarith
                            linarith
                          linarith
                        linarith
                      linarith
                    have h₂₄₅ : (Y : ℝ) ^ (18 / 23 : ℝ) / (p : ℝ) ^ (35 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := by
                      apply Real.le_sqrt_of_sq_le
                      linarith
                    linarith
                  linarith
                linarith
              have h₂₃₄ : (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
                have h₂₃₅ : (q : ℝ) < (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) := by linarith
                have h₂₃₆ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ (p : ℝ) := h₂₃₂
                have h₂₃₇ : (p : ℝ) ^ (-35 / 23 : ℝ) * (Y : ℝ) ^ (18 / 23 : ℝ) ≤ Real.sqrt (2 * Y / (p : ℝ)) := h₂₃₃
                have h₂₃₈ : (q : ℝ) < (p : ℝ) := by linarith
                have h₂₃₉ : (q : ℝ) < Real.sqrt (2 * Y / (p : ℝ)) := by linarith
                rw [min_lt_iff]
                exact ⟨h₂₃₈, h₂₃₉⟩
              exact h₂₃₄
            exact ⟨h₂₀, h₂₁, h₂₂, h₂₃⟩
        exact h₄
      exact h₂₁
    obtain ⟨Y₀, hY₀⟩ := h₂
    -- Choose N₀ such that localization N ε ≥ Y₀ for all N ≥ N₀
    have h₃ : ∃ (N₀ : ℝ), ∀ (N : ℝ), N₀ ≤ N → (localization N ε : ℝ) ≥ Y₀ := by
      have h₃₁ : 0 < (7 / 12 : ℝ) + ε := by linarith
      have h₃₂ : ∃ (N₀ : ℝ), ∀ (N : ℝ), N₀ ≤ N → (N : ℝ) ^ ((7 / 12 : ℝ) + ε) ≥ Y₀ := by
        -- Since the exponent is positive, N^(7/12+ε) → ∞ as N → ∞
        have h₃₃ : ∃ (N₀ : ℝ), ∀ (N : ℝ), N₀ ≤ N → (N : ℝ) ^ ((7 / 12 : ℝ) + ε) ≥ Y₀ := by
          -- Use the fact that rpow goes to infinity
          have h₃₄ : Filter.Tendsto (fun N : ℝ => (N : ℝ) ^ ((7 / 12 : ℝ) + ε)) Filter.atTop Filter.atTop := by
            apply Filter.tendsto_atTop_atTop.mpr
            intro b
            use max 1 (b ^ (1 / ((7 / 12 : ℝ) + ε)))
            intro N hN
            have h₃₅ : 1 ≤ (N : ℝ) := by linarith
            have h₃₆ : (b : ℝ) ^ (1 / ((7 / 12 : ℝ) + ε)) ≤ N := by linarith
            have h₃₇ : (b : ℝ) ^ (1 / ((7 / 12 : ℝ) + ε)) ≥ 0 := by positivity
            have h₃₈ : (N : ℝ) ^ ((7 / 12 : ℝ) + ε) ≥ b := by
              calc
                (N : ℝ) ^ ((7 / 12 : ℝ) + ε) ≥ ((b : ℝ) ^ (1 / ((7 / 12 : ℝ) + ε))) ^ ((7 / 12 : ℝ) + ε) := by
                  gcongr <;> nlinarith
                _ = (b : ℝ) := by
                  rw [← Real.rpow_mul (by positivity)]
                  field_simp [h₃₁.ne']
                  <;> ring_nf
                  <;> norm_num
                  <;> linarith
            linarith
          obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (h₃₄ (Y₀ : ℝ))
          refine' ⟨N₀, _⟩
          intro N hN
          exact hN₀ N hN
        exact h₃₃
      obtain ⟨N₀, hN₀⟩ := h₃₂
      refine' ⟨N₀, _⟩
      intro N hN
      have h₃₃ : (localization N ε : ℝ) = (N : ℝ) ^ ((7 / 12 : ℝ) + ε) := by
        simp [localization]
        <;> ring_nf
      rw [h₃₃]
      exact hN₀ N hN
    obtain ⟨N₀, hN₀⟩ := h₃
    use max N₀ 2
    intro N hN n hn
    have hN₂ : (2 : ℝ) ≤ N := by
      have h₁ := hN
      have h₂ : (max N₀ 2 : ℝ) ≤ N := h₁
      have h₃ : (2 : ℝ) ≤ max N₀ 2 := by apply le_max_right
      linarith
    have hY : (localization N ε : ℝ) ≥ Y₀ := hN₀ N (by linarith [le_max_left N₀ (2 : ℝ)])
    have hY_pos : 1 < (localization N ε : ℝ) := by
      have h₁ : (1 : ℝ) < localization N ε := by
        have h₂ : (1 : ℝ) < N := by linarith
        have h₃ : (0 : ℝ) < 7 / 12 + ε := by linarith
        exact Real.one_lt_rpow (by linarith) (by linarith)
      linarith
    -- Now we need to show that pairModel ≤ primeModel
    -- This follows because every term in pairModel also appears in primeModel
    have h₄ : pairModel labels11 N (localization N ε) n ≤ primeModel labels11 N (localization N ε) n := by
      have h₄₁ : ∀ (p q : ℕ), p ∈ Finset.range (⌊2 * (localization N ε)⌋₊ + 1) → q ∈ Finset.range (⌊2 * (localization N ε)⌋₊ + 1) →
          p.Prime → q.Prime → regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) →
          (if p.Prime ∧ q.Prime ∧ regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) ≤
          (if p.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
              q.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) ∧
              regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) := by
        intro p q hp hq hp' hq' hreg
        have h₁ : p.Prime := hp'
        have h₂ : q.Prime := hq'
        have h₃ : regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) := hreg
        have h₄ : (localization N ε : ℝ) ≥ Y₀ := hY
        have h₅ : 1 < (localization N ε : ℝ) := by linarith [hY_pos]
        -- Use the clipping conditions from h₂ to show the primeModel conditions hold
        have h₆ : ∃ (i : ℕ), i ∈ (labels11 : Finset ℕ) ∧ regionIndex (localization N ε) p q = i := by
          refine' ⟨regionIndex (localization N ε) p q, h₃, _⟩
          <;> simp_all
        have h₇ : (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
            (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) := by
          have h₇₁ : (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
              (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) := by
            have h₇₂ := hY₀ (localization N ε) h₄ p q hp' hq' h₆
            exact h₇₂
          exact h₇₁
        -- Now we know both if-conditions are true, so the values are equal
        have h₈ : (if p.Prime ∧ q.Prime ∧ regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) = (sifted N (localization N ε) n (p * q) q : ℝ) := by
          split_ifs <;> simp_all
        have h₉ : (if p.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
              q.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) ∧
              regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) = (sifted N (localization N ε) n (p * q) q : ℝ) := by
          split_ifs <;> norm_num at * <;> (try { contradiction }) <;> (try { linarith }) <;> (try { assumption }) <;> (try { aesop })
          <;> (try {
            constructor <;> (try { assumption }) <;> (try { linarith }) <;> (try { aesop })
          })
        rw [h₈, h₉]
      -- Now we can show the sum inequality by showing each term in pairModel is ≤ the corresponding term in primeModel
      have h₄₂ : pairModel labels11 N (localization N ε) n ≤ primeModel labels11 N (localization N ε) n := by
        -- The primeModel has a larger or equal summation domain for large N
        -- We use the fact that for n in the window, n ≥ N, and 2*localization N ε < n for large N
        have h₄₃ : ∀ (p q : ℕ), p ∈ Finset.range (⌊2 * (localization N ε)⌋₊ + 1) → q ∈ Finset.range (⌊2 * (localization N ε)⌋₊ + 1) →
            p.Prime → q.Prime → regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) →
            (if p.Prime ∧ q.Prime ∧ regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) ≤
            (if p.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
                q.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) ∧
                regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) := h₄₁
        -- The primeModel sums over p, q up to n, while pairModel sums up to 2Y
        -- For large N, 2Y < n, so the pairModel domain is a subset of primeModel domain
        have h₄₄ : (⌊2 * (localization N ε)⌋₊ : ℕ) < n + 1 := by
          have h₄₅ : (n : ℝ) > N := by
            obtain ⟨hnI, _⟩ := Finset.mem_filter.mp hn
            obtain ⟨hnI₁, hnI₂⟩ := Finset.mem_Ioc.mp hnI₁
            have h₄₆ : (⌊N⌋₊ : ℝ) < (n : ℝ) := by exact_mod_cast hnI₁
            have h₄₇ : (N : ℝ) ≤ (⌊N⌋₊ : ℝ) + 1 := by
              linarith [Nat.le_ceil N]
            have h₄₈ : (N : ℝ) < (n : ℝ) + 1 := by linarith
            have h₄₉ : (N : ℝ) ≤ (n : ℝ) := by
              by_contra h
              have h₅₀ : (n : ℝ) < N := by linarith
              have h₅₁ : (n : ℕ) < ⌈N⌉₊ := by
                apply Nat.lt_ceil.mp
                exact_mod_cast h₅₀
              have h₅₂ : (n : ℕ) ≤ ⌊N⌋₊ := by
                have h₅₃ : ⌈N⌉₊ ≤ ⌊N⌋₊ + 1 := by
                  simp [Nat.ceil_eq_iff, Nat.le_ceil]
                  <;> omega
                omega
              have h₅₄ : (n : ℝ) ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast h₅₂
              linarith
            linarith
          have h₄₅ : (2 : ℝ) * (localization N ε : ℝ) < (n : ℝ) := by
            have h₄₆ : (localization N ε : ℝ) = (N : ℝ) ^ ((7 / 12 : ℝ) + ε) := by
              simp [localization]
              <;> ring_nf
            have h₄₇ : (n : ℝ) ≥ N := by linarith
            have h₄₈ : (N : ℝ) ≥ max N₀ 2 := by exact_mod_cast (le_max_left N₀ (2 : ℝ)).trans hN
            have h₄₉ : (N : ℝ) ≥ 2 := by linarith [le_max_right N₀ (2 : ℝ)]
            have h₄₁₀ : (ε : ℝ) < 1 / 100 := hε₁
            have h₄₁₁ : (0 : ℝ) < ε := hε_pos
            have h₄₁₂ : (N : ℝ) ^ ((7 / 12 : ℝ) + ε) > 0 := by positivity
            -- Use the fact that N^(7/12+ε) grows slower than N for ε < 5/12
            have h₄₁₃ : (2 : ℝ) * (N : ℝ) ^ ((7 / 12 : ℝ) + ε) < (N : ℝ) := by
              have h₄₁₄ : (7 / 12 : ℝ) + ε < 1 := by linarith
              have h₄₁₅ : (N : ℝ) ≥ 2 := by linarith
              have h₄₁₆ : (N : ℝ) ^ ((7 / 12 : ℝ) + ε) < (N : ℝ) := by
                apply Real.rpow_lt_rpow (by linarith) (by linarith) (by linarith)
              nlinarith
            have h₄₁₄ : (2 : ℝ) * (localization N ε : ℝ) = (2 : ℝ) * (N : ℝ) ^ ((7 / 12 : ℝ) + ε) := by
              rw [h₄₆]
              <;> ring_nf
            rw [h₄₁₄]
            linarith
          have h₄₆ : (⌊2 * (localization N ε)⌋₊ : ℝ) ≤ 2 * (localization N ε : ℝ) := by
            exact Nat.le_ceil _
          have h₄₇ : (⌊2 * (localization N ε)⌋₊ : ℕ) < n + 1 := by
            have h₄₈ : (⌊2 * (localization N ε)⌋₊ : ℝ) < (n : ℝ) + 1 := by linarith
            have h₄₉ : (⌊2 * (localization N ε)⌋₊ : ℕ) < n + 1 := by
              norm_cast at h₄₈ ⊢
              <;> omega
            exact h₄₉
          exact h₄₇
        -- Since the summation domain of pairModel is a subset of primeModel, the sum is ≤
        calc
          pairModel labels11 N (localization N ε) n = ∑ p in Finset.range (⌊2 * (localization N ε)⌋₊ + 1), ∑ q in Finset.range (⌊2 * (localization N ε)⌋₊ + 1),
              (if p.Prime ∧ q.Prime ∧ regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) := by
            simp [pairModel]
            <;> ring_nf
          _ ≤ ∑ p in Finset.range (n + 1), ∑ q in Finset.range (n + 1),
              (if p.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
                  q.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) ∧
                  regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) := by
            -- Use the fact that the pairModel domain is a subset of the primeModel domain
            have h₅₀ : ∀ (p q : ℕ), p ∈ Finset.range (⌊2 * (localization N ε)⌋₊ + 1) → q ∈ Finset.range (⌊2 * (localization N ε)⌋₊ + 1) →
                p.Prime → q.Prime → regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) →
                (if p.Prime ∧ q.Prime ∧ regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) ≤
                (if p.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
                    q.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) ∧
                    regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) := h₄₃
            have h₅₁ : Finset.range (⌊2 * (localization N ε)⌋₊ + 1) ⊆ Finset.range (n + 1) := by
              intro p hp
              have h₅₂ : p < ⌊2 * (localization N ε)⌋₊ + 1 := Finset.mem_range.mp hp
              have h₅₃ : p < n + 1 := by
                have h₅₄ : p ≤ ⌊2 * (localization N ε)⌋₊ := by omega
                have h₅₅ : (⌊2 * (localization N ε)⌋₊ : ℕ) < n + 1 := h₄₄
                omega
              exact Finset.mem_range.mpr h₅₃
            calc
              ∑ p in Finset.range (⌊2 * (localization N ε)⌋₊ + 1), ∑ q in Finset.range (⌊2 * (localization N ε)⌋₊ + 1),
                  (if p.Prime ∧ q.Prime ∧ regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) ≤
                  ∑ p in Finset.range (⌊2 * (localization N ε)⌋₊ + 1), ∑ q in Finset.range (⌊2 * (localization N ε)⌋₊ + 1),
                      (if p.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
                          q.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) ∧
                          regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) := by
                apply Finset.sum_le_sum
                intro p hp
                apply Finset.sum_le_sum
                intro q hq
                by_cases hp' : p.Prime <;> by_cases hq' : q.Prime <;> by_cases hreg : regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) <;> simp_all [h₅₀]
                <;> norm_num at * <;> (try { linarith }) <;> (try { aesop })
              _ ≤ ∑ p in Finset.range (n + 1), ∑ q in Finset.range (n + 1),
                  (if p.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * (localization N ε : ℝ)) ∧
                      q.Prime ∧ (localization N ε : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * (localization N ε : ℝ) / (p : ℝ))) ∧
                      regionIndex (localization N ε) p q ∈ (labels11 : Finset ℕ) then (sifted N (localization N ε) n (p * q) q : ℝ) else 0) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg h₅₁
                intro p hp
                apply Finset.sum_le_sum_of_subset_of_nonneg (by
                  intro q hq
                  have h₅₂ : q < ⌊2 * (localization N ε)⌋₊ + 1 := Finset.mem_range.mp hq
                  have h₅₃ : q < n + 1 := by
                    have h₅₄ : q ≤ ⌊2 * (localization N ε)⌋₊ := by omega
                    have h₅₅ : (⌊2 * (localization N ε)⌋₊ : ℕ) < n + 1 := h₄₄
                    omega
                  exact Finset.mem_range.mpr h₅₃)
                intro q hq
                split_ifs <;> simp_all [Finset.mem_range]
                <;> positivity
          _ = primeModel labels11 N (localization N ε) n := by
            simp [primeModel]
            <;> ring_nf
            <;> simp_all [Finset.sum_range_succ, Finset.filter_eq']
            <;> aesop
      exact h₄₂
    exact h₄
    exact h₄
  obtain ⟨N₀, hN₀⟩ := h₁
  exact ⟨N₀, hN₀⟩

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
