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

/-- Pages 267 to 269 display 52: the least matching region satisfies its own six defining inequalities. -/
theorem regionIndex_spec (Y : ℝ) (p q : ℕ) (h : regionIndex Y p q ≠ 0) :
    Y ^ (regionData (regionIndex Y p q) 0 : ℝ) < (p : ℝ) ∧
      (p : ℝ) ≤ Y ^ (regionData (regionIndex Y p q) 1 : ℝ) ∧
      (p : ℝ) ^ (regionData (regionIndex Y p q) 2 : ℝ) *
        Y ^ (regionData (regionIndex Y p q) 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData (regionIndex Y p q) 4 : ℝ) *
        Y ^ (regionData (regionIndex Y p q) 5 : ℝ) := by
  unfold regionIndex at h ⊢
  split_ifs at h ⊢ with hex
  · exact (Nat.find_spec hex).2
  · exact absurd rfl h

/-- Pages 267 to 269: the region inequalities in logarithmic form. -/
theorem region_logs (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : regionIndex Y p q ≠ 0) :
    (regionData (regionIndex Y p q) 0 : ℝ) * Real.log Y < Real.log p ∧
      Real.log p ≤ (regionData (regionIndex Y p q) 1 : ℝ) * Real.log Y ∧
      (regionData (regionIndex Y p q) 2 : ℝ) * Real.log p +
        (regionData (regionIndex Y p q) 3 : ℝ) * Real.log Y < Real.log q ∧
      Real.log q < (regionData (regionIndex Y p q) 4 : ℝ) * Real.log p +
        (regionData (regionIndex Y p q) 5 : ℝ) * Real.log Y := by
  obtain ⟨h1, h2, h3, h4⟩ := regionIndex_spec Y p q h
  have hY0 : 0 < Y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  set i := regionIndex Y p q
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Real.log_lt_log (rpow_pos_of_pos hY0 _) h1
    rwa [Real.log_rpow hY0] at this
  · have := Real.log_le_log hp0 h2
    rwa [Real.log_rpow hY0] at this
  · have := Real.log_lt_log (by positivity) h3
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hp0,
      Real.log_rpow hY0] at this
  · have := Real.log_lt_log hq0 h4
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hp0,
      Real.log_rpow hY0] at this

/-- Page 280: the clipping inequalities follow from their logarithmic forms. -/
theorem clip_of_logs (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (g1 : (16 / 135 : ℝ) * Real.log Y < Real.log p)
    (g2 : 2 * Real.log p ≤ Real.log 2 + Real.log Y)
    (g3 : (16 / 135 : ℝ) * Real.log Y < Real.log q)
    (g4 : Real.log q < Real.log p)
    (g5 : 2 * Real.log q + Real.log p < Real.log 2 + Real.log Y) :
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
  have hY0 : 0 < Y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  refine ⟨?_, ?_, ?_, lt_min ?_ ?_⟩
  · rw [← Real.log_lt_log_iff (rpow_pos_of_pos hY0 _) hp0, Real.log_rpow hY0]; exact g1
  · rw [Real.le_sqrt hp0.le (by positivity)]
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) hY0.ne']
    push_cast; linarith
  · rw [← Real.log_lt_log_iff (rpow_pos_of_pos hY0 _) hq0, Real.log_rpow hY0]; exact g3
  · rwa [← Real.log_lt_log_iff hq0 hp0]
  · rw [Real.lt_sqrt hq0.le]
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow,
      Real.log_div (by positivity) hp0.ne', Real.log_mul (by norm_num) hY0.ne']
    push_cast; linarith


/-- Page 280: every prime pair of regions 33, 36, 38, 40, 42, 46 and 49 lies in the clipped recovery domain. -/
theorem clip11 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : regionIndex Y p q ∈ labels11) :
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
  have h0 : regionIndex Y p q ≠ 0 := by
    intro h0; rw [h0] at h; simp [labels11] at h
  obtain ⟨l1, l2, l3, l4⟩ := region_logs Y hY p q hp hq h0
  have hL : 0 < Real.log Y := Real.log_pos hY
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  generalize regionIndex Y p q = i at h l1 l2 l3 l4
  simp only [labels11, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [show regionData 33 0 = (1649/4752 : ℚ) from rfl, show regionData 33 1 = (25/72 : ℚ) from rfl, show regionData 33 2 = (-70/59 : ℚ) from rfl, show regionData 33 3 = (34/59 : ℚ) from rfl, show regionData 33 4 = (-58/49 : ℚ) from rfl, show regionData 33 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith
  · simp only [show regionData 36 0 = (25/72 : ℚ) from rfl, show regionData 36 1 = (10/27 : ℚ) from rfl, show regionData 36 2 = (-70/59 : ℚ) from rfl, show regionData 36 3 = (34/59 : ℚ) from rfl, show regionData 36 4 = (-58/49 : ℚ) from rfl, show regionData 36 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith
  · simp only [show regionData 38 0 = (10/27 : ℚ) from rfl, show regionData 38 1 = (617/1620 : ℚ) from rfl, show regionData 38 2 = (-70/59 : ℚ) from rfl, show regionData 38 3 = (34/59 : ℚ) from rfl, show regionData 38 4 = (-58/49 : ℚ) from rfl, show regionData 38 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith
  · simp only [show regionData 40 0 = (617/1620 : ℚ) from rfl, show regionData 40 1 = (1823/4725 : ℚ) from rfl, show regionData 40 2 = (-70/59 : ℚ) from rfl, show regionData 40 3 = (34/59 : ℚ) from rfl, show regionData 40 4 = (-58/49 : ℚ) from rfl, show regionData 40 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith
  · simp only [show regionData 42 0 = (1823/4725 : ℚ) from rfl, show regionData 42 1 = (3041/7830 : ℚ) from rfl, show regionData 42 2 = (0 : ℚ) from rfl, show regionData 42 3 = (16/135 : ℚ) from rfl, show regionData 42 4 = (-58/49 : ℚ) from rfl, show regionData 42 5 = (85/147 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith
  · simp only [show regionData 46 0 = (11/27 : ℚ) from rfl, show regionData 46 1 = (34/81 : ℚ) from rfl, show regionData 46 2 = (-29/19 : ℚ) from rfl, show regionData 46 3 = (89/114 : ℚ) from rfl, show regionData 46 4 = (-35/23 : ℚ) from rfl, show regionData 46 5 = (18/23 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith
  · simp only [show regionData 49 0 = (34/81 : ℚ) from rfl, show regionData 49 1 = (49/114 : ℚ) from rfl, show regionData 49 2 = (-29/19 : ℚ) from rfl, show regionData 49 3 = (89/114 : ℚ) from rfl, show regionData 49 4 = (-35/23 : ℚ) from rfl, show regionData 49 5 = (18/23 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith

/-- Page 282: every prime pair of regions 53 and 66 lies in the clipped recovery domain. -/
theorem clip12 (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : regionIndex Y p q ∈ labels12) :
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by
  have h0 : regionIndex Y p q ≠ 0 := by
    intro h0; rw [h0] at h; simp [labels12] at h
  obtain ⟨l1, l2, l3, l4⟩ := region_logs Y hY p q hp hq h0
  have hL : 0 < Real.log Y := Real.log_pos hY
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  generalize regionIndex Y p q = i at h l1 l2 l3 l4
  simp only [labels12, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl
  · simp only [show regionData 53 0 = (3397/7830 : ℚ) from rfl, show regionData 53 1 = (4/9 : ℚ) from rfl, show regionData 53 2 = (-35/12 : ℚ) from rfl, show regionData 53 3 = (17/12 : ℚ) from rfl, show regionData 53 4 = (-29/10 : ℚ) from rfl, show regionData 53 5 = (17/12 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith
  · simp only [show regionData 66 0 = (211/432 : ℚ) from rfl, show regionData 66 1 = (281/570 : ℚ) from rfl, show regionData 66 2 = (-58/9 : ℚ) from rfl, show regionData 66 3 = (89/27 : ℚ) from rfl, show regionData 66 4 = (-70/11 : ℚ) from rfl, show regionData 66 5 = (36/11 : ℚ) from rfl] at l1 l2 l3 l4
    push_cast at l1 l2 l3 l4
    apply clip_of_logs Y hY p q hp hq <;> linarith

/-- Page 263: a nonzero count S of A_d and z forces d at most n. -/
theorem sifted_ne_zero_le (N Y : ℝ) (n d : ℕ) (z : ℝ) (h : sifted N Y n d z ≠ 0) : d ≤ n := by
  unfold sifted at h
  obtain ⟨a, ha⟩ := Finset.card_ne_zero.mp h
  obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha1
  exact (Nat.le_of_dvd (by omega) ha2.1).trans h2

/-- Page 280: a family whose prime pairs all lie in the clipped domain has its unclipped prime sum below the clipped prime model. -/
theorem pairModel_le_primeModel_of_clip (labels : Finset ℕ) (N Y : ℝ) (n : ℕ)
    (hclip : ∀ p q : ℕ, p.Prime → q.Prime → regionIndex Y p q ∈ labels →
      Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))) :
    pairModel labels N Y n ≤ primeModel labels N Y n := by
  set F : ℕ → ℕ → ℝ := fun p q =>
    if p.Prime ∧ q.Prime ∧ regionIndex Y p q ∈ labels then (sifted N Y n (p * q) q : ℝ) else 0
    with hF
  have hF0 : ∀ p q, 0 ≤ F p q := fun p q => by simp only [hF]; split_ifs <;> positivity
  have hFne : ∀ p q, F p q ≠ 0 → p.Prime ∧ q.Prime ∧ regionIndex Y p q ∈ labels ∧
      sifted N Y n (p * q) q ≠ 0 := by
    intro p q h
    simp only [hF] at h
    split_ifs at h with hc
    · exact ⟨hc.1, hc.2.1, hc.2.2, fun h0 => h (by simp [h0])⟩
    · exact absurd rfl h
  have hA : pairModel labels N Y n ≤ ∑ x ∈ range (n + 1) ×ˢ range (n + 1), F x.1 x.2 := by
    have e : pairModel labels N Y n =
        ∑ x ∈ range (⌊2 * Y⌋₊ + 1) ×ˢ range (⌊2 * Y⌋₊ + 1), F x.1 x.2 := by
      rw [sum_product]; rfl
    rw [e, ← sum_filter_ne_zero]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      obtain ⟨-, hx⟩ := mem_filter.mp hx
      obtain ⟨hp, hq, -, hs⟩ := hFne _ _ hx
      have hle := sifted_ne_zero_le N Y n _ _ hs
      have hp1 := hp.one_le
      have hq1 := hq.one_le
      have : x.1 ≤ n := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hle
      have : x.2 ≤ n := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hle
      exact mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩
    · intro x _ _; exact hF0 _ _
  refine hA.trans ?_
  rw [sum_product]
  unfold primeModel
  rw [← sum_filter_of_ne (p := fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y))]
  · apply sum_le_sum
    intro p _
    rw [← sum_filter_of_ne (p := fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))))]
    · apply sum_le_sum
      intro q _
      simp only [hF]
      split_ifs <;> first | exact le_rfl | positivity | (exfalso; tauto)
    · intro q _ hq
      obtain ⟨hp, hq', hl, -⟩ := hFne _ _ hq
      obtain ⟨-, -, c3, c4⟩ := hclip p q hp hq' hl
      exact ⟨hq', c3, c4⟩
  · intro p _ hp
    obtain ⟨q, _, hq⟩ := exists_ne_zero_of_sum_ne_zero hp
    obtain ⟨hp', hq', hl, -⟩ := hFne _ _ hq
    obtain ⟨c1, c2, -, -⟩ := hclip p q hp' hq' hl
    exact ⟨hp', c1, c2⟩

/-- Page 208: Y exceeds 1 once N is at least 2. -/
theorem one_lt_localization (N ε : ℝ) (hN : 2 ≤ N) (hε : 0 < ε) : 1 < localization N ε := by
  unfold localization
  exact Real.one_lt_rpow (by linarith) (by linarith)

/-- PROVED, formerly LEAF: Jia page 280 clipping, for n in the basic interval every prime pair of regions 33,
36, 38, 40, 42, 46 and 49 satisfies Y^(16/135) < q < min p (sqrt (2Y/p)) and p ≤ sqrt (2Y),
so the unclipped prime sum is a subsum of the clipped prime model. MEDIUM -/
theorem pairModel11_le_primeModel :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ n ∈ window N ε,
        pairModel labels11 N (localization N ε) n ≤ primeModel labels11 N (localization N ε) n :=
  ⟨1, one_pos, fun ε hε _ => ⟨2, fun N hN n _ =>
    pairModel_le_primeModel_of_clip labels11 N _ n
      (clip11 _ (one_lt_localization N ε hN hε))⟩⟩

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
#print axioms clip11
#print axioms clip12
#print axioms pairModel_le_primeModel_of_clip
#print axioms pairModel11_le_primeModel
#print axioms region_transfer11
#print axioms prime_to_rough11_from_leaves
end
end LeanLab.Languasco2004.Feed564bPrime
