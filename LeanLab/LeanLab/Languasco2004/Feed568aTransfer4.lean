/-
Jia 1996 pages 263 and 277 to 279, displays 48 and 53 to 56: split of
`Decomp568a.region4_transfer_exception` into the region bookkeeping of display 52
and the lower and upper halves of the prime to integer model transfer.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The LEAF region4_piece_eq is proved; the two transfer halves remain OPEN.
The assembly below is proved from them.
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

/-- Pages 267 to 269 display 52: for Y at least one, the least region label of a pair
of positive integers is 4 exactly on region D4, since D1 and D2 have smaller p and
D3 has smaller q. -/
theorem regionIndex_eq_four_iff {Y : ℝ} (hY : 1 ≤ Y) (p q : ℕ) (hp : 0 < p) :
    regionIndex Y p q = 4 ↔
      (Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ) ∧
        (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p) := by
  have hY0 : 0 < Y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h4 : ∀ i, i = 4 → ((i ∈ Icc 1 69 ∧
      Y ^ (regionData i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (regionData i 1 : ℝ) ∧
      (p : ℝ) ^ (regionData i 2 : ℝ) * Y ^ (regionData i 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData i 4 : ℝ) * Y ^ (regionData i 5 : ℝ)) ↔
      (Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ) ∧
        (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p)) := by
    rintro i rfl
    simp [regionData, Real.rpow_neg_one]
  -- the three smaller labels fail on D4
  have hsmall : (Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ) ∧
        (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p) → ∀ m < 4, ¬ (m ∈ Icc 1 69 ∧
      Y ^ (regionData m 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (regionData m 1 : ℝ) ∧
      (p : ℝ) ^ (regionData m 2 : ℝ) * Y ^ (regionData m 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData m 4 : ℝ) * Y ^ (regionData m 5 : ℝ)) := by
    rintro ⟨hpl, hpu, hql, hqu⟩ m hm ⟨hmI, h0, h1, h2, h3⟩
    interval_cases m
    · simp at hmI
    · simp [regionData] at h1
      have : Y ^ (89 / 462 : ℝ) ≤ Y ^ (41 / 180 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
      linarith
    · simp [regionData] at h1
      linarith
    · simp [regionData] at h3
      -- p^(-29/48) Y^(89/288) ≤ p⁻¹ Y^(41/90)
      have hsplit : (p : ℝ) ^ (-29 / 48 : ℝ) = (p : ℝ)⁻¹ * (p : ℝ) ^ (19 / 48 : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hp0]; norm_num
      have hpow : (p : ℝ) ^ (19 / 48 : ℝ) ≤ Y ^ ((8 / 33 : ℝ) * (19 / 48)) := by
        rw [Real.rpow_mul hY0.le]
        exact Real.rpow_le_rpow hp0.le hpu (by norm_num)
      have hY2 : Y ^ ((8 / 33 : ℝ) * (19 / 48)) * Y ^ (89 / 288 : ℝ) ≤ Y ^ (41 / 90 : ℝ) := by
        rw [← Real.rpow_add hY0]
        exact Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
      have hinv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
      have key : (p : ℝ) ^ (-29 / 48 : ℝ) * Y ^ (89 / 288 : ℝ) ≤ (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) := by
        rw [hsplit, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hinv.le
        calc (p : ℝ) ^ (19 / 48 : ℝ) * Y ^ (89 / 288 : ℝ)
            ≤ Y ^ ((8 / 33 : ℝ) * (19 / 48)) * Y ^ (89 / 288 : ℝ) :=
              mul_le_mul_of_nonneg_right hpow (by positivity)
          _ ≤ _ := hY2
      have : (q : ℝ) < (p : ℝ) ^ (-29 / 48 : ℝ) * Y ^ (89 / 288 : ℝ) := by
        convert h3 using 3
      linarith
  unfold regionIndex
  constructor
  · intro h
    split_ifs at h with hex
    · have hs := Nat.find_spec hex
      rw [h] at hs
      exact (h4 4 rfl).mp hs
  · intro hD
    have hex : ∃ i : ℕ, i ∈ Icc 1 69 ∧
      Y ^ (regionData i 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (regionData i 1 : ℝ) ∧
      (p : ℝ) ^ (regionData i 2 : ℝ) * Y ^ (regionData i 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData i 4 : ℝ) * Y ^ (regionData i 5 : ℝ) :=
      ⟨4, (h4 4 rfl).mpr hD⟩
    rw [dif_pos hex, Nat.find_eq_iff]
    exact ⟨(h4 4 rfl).mpr hD, hsmall hD⟩

/-- LEAF: Jia pages 267 to 269 display 52 and page 279, the selected Omega4 piece is the
sum over the full Omega4 domain. MEDIUM.
Regions 1 to 3 of the least label convention do not meet region 4, label 4 lies in group 3,
and for large N every recovery cap and the range caps n + 1 and 2 Y + 1 are inactive
on the Omega4 domain, since Y ^ (41/90) / p exceeds Y ^ (16/135) and p cubed is below 2 Y. -/
theorem region4_piece_eq :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 12 → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ n ∈ window N ε,
      pieceSum 3 4 true N (localization N ε) n = omega4Sum N (localization N ε) n := by
  intro ε hε hε12
  refine ⟨1, fun N hN n hn => ?_⟩
  set Y := localization N ε with hYdef
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN (by linarith)
  have hY0 : 0 < Y := by linarith
  have hYN : Y ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN (show 7 / 12 + ε ≤ (1 : ℝ) by linarith)
    simpa [hYdef, localization] using this
  have hnN : N < (n : ℝ) := by
    simp only [window, mem_filter, mem_Ioc] at hn
    exact Nat.lt_of_floor_lt hn.1.1
  -- powers of Y^(8/33)
  have hpowY : ∀ k : ℕ, (k : ℝ) * (8 / 33) ≤ 1 → (Y ^ (8 / 33 : ℝ)) ^ k ≤ Y := by
    intro k hk
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    calc Y ^ ((8 / 33 : ℝ) * k) ≤ Y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
      _ = Y := Real.rpow_one Y
  have h833 : Y ^ (8 / 33 : ℝ) ≤ Y := by simpa using hpowY 1 (by norm_num)
  have hM : ∀ x : ℝ, x ≤ Y ^ (8 / 33 : ℝ) → x < ((⌊2 * Y⌋₊ + 1 : ℕ) : ℝ) := by
    intro x hx
    have := Nat.lt_floor_add_one (2 * Y)
    push_cast
    linarith
  have hn1 : ∀ x : ℝ, x ≤ Y ^ (8 / 33 : ℝ) → x < ((n + 1 : ℕ) : ℝ) := by
    intro x hx
    push_cast
    linarith
  unfold pieceSum omega4Sum
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    obtain ⟨_, hpr, hpl, hpu⟩ := hp
    have hp0 : (0 : ℝ) ≤ p := by positivity
    refine ⟨?_, hpr, ?_, ?_⟩
    · exact_mod_cast hn1 p hpu
    · have : Y ^ (16 / 135 : ℝ) ≤ Y ^ (41 / 180 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
      linarith
    · rw [Real.le_sqrt hp0 (by linarith)]
      have h2 : (p : ℝ) ^ 2 ≤ (Y ^ (8 / 33 : ℝ)) ^ 2 := pow_le_pow_left₀ hp0 hpu 2
      have := hpowY 2 (by norm_num)
      linarith
  · intro p hp
    simp only [mem_sdiff] at hp
    obtain ⟨hp1, hp2⟩ := hp
    apply Finset.sum_eq_zero
    intro q hq
    rw [if_neg]
    rintro ⟨_, h4⟩
    have h4' : regionIndex Y p q = 4 := by simpa using h4
    simp only [mem_filter, mem_range] at hp1 hq
    have hppos : 0 < p := hp1.2.1.pos
    have hD := (regionIndex_eq_four_iff hY1 p q hppos).mp h4'
    apply hp2
    simp only [mem_filter, mem_range]
    exact ⟨by exact_mod_cast hM p hD.2.1, hp1.2.1, hD.1, hD.2.1⟩
  · intro p hp
    simp only [mem_filter, mem_range] at hp
    obtain ⟨_, hpr, hpl, hpu⟩ := hp
    have hppos : 0 < p := hpr.pos
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hppos
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext q
    simp only [mem_filter, mem_range]
    have hg : groupOf 4 = 3 := by simp [groupOf]
    constructor
    · rintro ⟨_, hqr, hql, hqu⟩
      have hD : regionIndex Y p q = 4 :=
        (regionIndex_eq_four_iff hY1 p q hppos).mpr ⟨hpl, hpu, hql, hqu⟩
      refine ⟨⟨?_, hqr, ?_, ?_⟩, ?_⟩
      · have := hn1 p hpu
        have : (q : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
        exact_mod_cast this
      · -- q > p⁻¹ Y^(41/90) ≥ Y^(41/90 - 8/33) ≥ Y^(16/135)
        have h1 : Y ^ (41 / 90 - 8 / 33 : ℝ) ≤ (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) := by
          rw [Real.rpow_sub hY0, div_eq_mul_inv, mul_comm]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact inv_anti₀ hp0 hpu
        have h2 : Y ^ (16 / 135 : ℝ) ≤ Y ^ (41 / 90 - 8 / 33 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
        linarith
      · rw [lt_min_iff]
        refine ⟨hqu, lt_of_lt_of_le hqu ?_⟩
        rw [Real.le_sqrt hp0.le (by positivity), le_div_iff₀ hp0]
        have h3 : (p : ℝ) ^ 3 ≤ (Y ^ (8 / 33 : ℝ)) ^ 3 := pow_le_pow_left₀ hp0.le hpu 3
        have := hpowY 3 (by norm_num)
        nlinarith
      · simp [hD, hg]
    · rintro ⟨⟨_, hqr, _, _⟩, h4⟩
      have h4' : regionIndex Y p q = 4 := by simpa using h4.2
      have hD := (regionIndex_eq_four_iff hY1 p q hppos).mp h4'
      refine ⟨?_, hqr, hD.2.2.1, hD.2.2.2⟩
      have := hM p hpu
      have : (q : ℝ) < ((⌊2 * Y⌋₊ + 1 : ℕ) : ℝ) := by linarith [hD.2.2.2]
      exact_mod_cast this

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
