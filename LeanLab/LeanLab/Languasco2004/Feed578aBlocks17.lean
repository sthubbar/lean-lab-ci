/-
Jia 1996 page 253, Lemma 17, with the union over dyadic blocks used on page 283.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Feed578aPair.lemma17_blocks_uniform into a uniform Lemma 17 LEAF and a
proved union bound assembly. The uniform Lemma 17 remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp565c
import LeanLab.Languasco2004.Decomp316d

namespace LeanLab.Languasco2004.Feed578aBlocks17
open Finset Real Filter Decomp279a Decomp316a Source565 Decomp565c Decomp316d
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 253 Lemma 17 with implicit constants depending only on epsilon and B, HARD.
Lemma 17 on page 253 is stated for any dyadic M at most Y to 19/36 and any weights bounded
by one, with implied constants depending only on epsilon and B; its proof from Lemmas 6 and 15
and the large sieve is a mean value argument uniform in the weights. Here the constants
C, D and the threshold N₀ are chosen before M and the weights. -/
theorem lemma17_uniform :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ M : ℝ, 1 ≤ M → M ≤ (localization N ε) ^ (19 / 36 : ℝ) →
      ∀ a : ℕ → ℝ, (∀ m : ℕ, |a m| ≤ 1) →
      (((window N ε).filter (fun n =>
        D * localization N ε / log N ^ B <
          |progressionRemainder N (localization N ε) M n a|)).card : ℝ) ≤
      C * windowLength N ε / log N ^ B := by sorry

/-- Page 283 support: the number of blocks is at most a fixed multiple of log N. -/
theorem ceil_blocks_le (K L : ℝ) (hL : 1 ≤ L) :
    ((⌈K * L⌉₊ : ℕ) : ℝ) ≤ (|K| + 1) * L := by
  have hL0 : 0 ≤ L := by linarith
  have h1 : ((⌈K * L⌉₊ : ℕ) : ℝ) ≤ ((⌈|K| * L⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self K) hL0)
  have h2 : ((⌈|K| * L⌉₊ : ℕ) : ℝ) < |K| * L + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (abs_nonneg K) hL0)
  nlinarith [abs_nonneg K]

/-- Jia page 253 Lemma 17 and page 283: exact type of Feed578aPair.lemma17_blocks_uniform.
CONDITIONAL ON the LEAF lemma17_uniform. The union over the blocks at exponent B plus 3
uses the lower bound tailProduct times Y over log N squared for the scale on even n. -/
theorem lemma17_blocks_uniform_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ (K : ℝ) (M : ℕ → ℝ → ℝ) (a : ℕ → ℝ → ℕ → ℝ),
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N → 1 ≤ M j N ∧ M j N ≤ (localization N ε) ^ (19 / 36 : ℝ)) →
      (∀ j : ℕ, ∀ N : ℝ, ∀ m : ℕ, |a j N m| ≤ 1) →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000001 * scale N (localization N ε) n <
          ∑ j ∈ range ⌈K * log N⌉₊,
            |progressionRemainder N (localization N ε) (M j N) n (a j N)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e, he, hL17⟩ := lemma17_uniform
  refine ⟨min e (1 / 12), lt_min he (by norm_num), ?_⟩
  intro ε B hε hεe hB K M a hM ha
  have hεe1 : ε < e := hεe.trans_le (min_le_left _ _)
  have hε12 : ε < 1 / 12 := hεe.trans_le (min_le_right _ _)
  obtain ⟨C, D, N₀, hD, hC⟩ := hL17 ε (B + 3) hε hεe1 (by linarith)
  -- the size of log N to the B needed to absorb the block count
  set c : ℝ := (|K| + 1) * D / (0.00000001 * tailProduct) with hc
  have htend : Tendsto (fun N : ℝ => log N ^ B) atTop atTop :=
    (tendsto_rpow_atTop hB).comp tendsto_log_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (htend.eventually_ge_atTop c)
  refine ⟨(|K| + 1) * |C|, max (max N₀ N₁) 3, ?_⟩
  intro N hN
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN1 : N₁ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hNp : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log N := by
    rw [Real.le_log_iff_exp_le hNp]
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le.trans hN3
  have hL : 0 < log N := by linarith
  set L := log N with hLdef
  set Y := localization N ε with hYdef
  set A := windowLength N ε with hAdef
  have hYp : 1 < Y := Real.one_lt_rpow (by linarith) (by positivity : (0 : ℝ) < 7 / 12 + ε)
  have hA : 0 ≤ A := Real.rpow_nonneg hNp.le _
  have hLB : 0 < L ^ B := Real.rpow_pos_of_pos hL _
  have hLB3 : L ^ (B + 3) = L ^ B * L ^ 3 := by
    rw [Real.rpow_add hL]; norm_cast
  have hcL : c ≤ L ^ B := hN₁ N hN1
  set k : ℕ := ⌈K * L⌉₊ with hk
  have hkL : (k : ℝ) ≤ (|K| + 1) * L := ceil_blocks_le K L hL1
  have htP := tailProduct_pos
  -- block thresholds sum to at most 0.00000001 times the scale on even n
  have hsum_small : ∀ n : ℕ, Even n →
      (k : ℝ) * (D * Y / L ^ (B + 3)) ≤ 0.00000001 * scale N Y n := by
    intro n hn
    have hLY : 0 < log Y := Real.log_pos hYp
    have hlogY : log Y ≤ L := by
      rw [hYdef, localization, Real.log_rpow hNp]
      nlinarith
    have hscale := scale_pos (N := N) (Y := Y) n hn (by linarith) hYp
    have hmain : tailProduct * Y ≤ scale N Y n * L ^ 2 := by
      calc tailProduct * Y ≤ singular n * Y :=
             mul_le_mul_of_nonneg_right (tailProduct_le_singular n hn) (by linarith)
           _ = scale N Y n * (log Y * L) := by
             unfold scale
             rw [div_mul_cancel₀ _ (mul_ne_zero hLY.ne' hL.ne')]
           _ ≤ scale N Y n * L ^ 2 :=
             mul_le_mul_of_nonneg_left (by nlinarith) hscale.le
    have hcL' : (|K| + 1) * D ≤ 0.00000001 * tailProduct * L ^ B := by
      have h := mul_le_mul_of_nonneg_left hcL (by positivity : (0 : ℝ) ≤ 0.00000001 * tailProduct)
      rw [hc, mul_div_cancel₀ _ (by positivity)] at h
      exact h
    have hY0 : 0 ≤ Y := by linarith
    rw [hLB3]
    have hstep : (k : ℝ) * (D * Y / (L ^ B * L ^ 3)) ≤
        ((|K| + 1) * L) * (D * Y / (L ^ B * L ^ 3)) :=
      mul_le_mul_of_nonneg_right hkL (by positivity)
    refine hstep.trans ?_
    have heq : ((|K| + 1) * L) * (D * Y / (L ^ B * L ^ 3)) =
        ((|K| + 1) * D) * Y / (L ^ B * L ^ 2) := by
      field_simp
    rw [heq, div_le_iff₀ (by positivity)]
    calc (|K| + 1) * D * Y ≤ (0.00000001 * tailProduct * L ^ B) * Y :=
           mul_le_mul_of_nonneg_right hcL' hY0
         _ = 0.00000001 * L ^ B * (tailProduct * Y) := by ring
         _ ≤ 0.00000001 * L ^ B * (scale N Y n * L ^ 2) :=
           mul_le_mul_of_nonneg_left hmain (by positivity)
         _ = 0.00000001 * scale N Y n * (L ^ B * L ^ 2) := by ring
  -- the exceptional set lies in the union of the block exceptional sets
  set E : ℕ → Finset ℕ := fun j => (window N ε).filter (fun n =>
    D * Y / L ^ (B + 3) < |progressionRemainder N Y (M j N) n (a j N)|) with hE
  have hsub : (window N ε).filter (fun n =>
      0.00000001 * scale N Y n <
        ∑ j ∈ range k, |progressionRemainder N Y (M j N) n (a j N)|) ⊆
      (range k).biUnion E := by
    intro n hn
    obtain ⟨hw, hbig⟩ := mem_filter.mp hn
    have hev : Even n := (mem_filter.mp hw).2
    by_contra hnot
    have hall : ∀ j ∈ range k,
        |progressionRemainder N Y (M j N) n (a j N)| ≤ D * Y / L ^ (B + 3) := by
      intro j hj
      by_contra hlt
      exact hnot (mem_biUnion.mpr ⟨j, hj, mem_filter.mpr ⟨hw, lt_of_not_ge hlt⟩⟩)
    have hle := Finset.sum_le_card_nsmul (range k) _ _ hall
    rw [card_range, nsmul_eq_mul] at hle
    linarith [hsum_small n hev]
  have hcardE : ∀ j ∈ range k, ((E j).card : ℝ) ≤ |C| * A / L ^ (B + 3) := by
    intro j _
    obtain ⟨hM1, hM2⟩ := hM j N (by linarith)
    refine (hC N hN0 (M j N) hM1 hM2 (a j N) (ha j N)).trans ?_
    have hpos : 0 < L ^ (B + 3) := Real.rpow_pos_of_pos hL _
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hA) hpos.le
  have hcount : (((window N ε).filter (fun n =>
      0.00000001 * scale N Y n <
        ∑ j ∈ range k, |progressionRemainder N Y (M j N) n (a j N)|)).card : ℝ) ≤
      (k : ℝ) * (|C| * A / L ^ (B + 3)) := by
    have h1 := card_le_card hsub
    have h2 := card_biUnion_le (s := range k) (t := E)
    have h3 : (((range k).biUnion E).card : ℝ) ≤ ∑ j ∈ range k, ((E j).card : ℝ) := by
      exact_mod_cast h2
    have h4 := Finset.sum_le_card_nsmul (range k) (fun j => ((E j).card : ℝ)) _ hcardE
    rw [card_range, nsmul_eq_mul] at h4
    have h1' : (((window N ε).filter (fun n =>
      0.00000001 * scale N Y n <
        ∑ j ∈ range k, |progressionRemainder N Y (M j N) n (a j N)|)).card : ℝ) ≤
        (((range k).biUnion E).card : ℝ) := by exact_mod_cast h1
    linarith
  refine hcount.trans ?_
  rw [hLB3]
  have hx : 0 ≤ |C| * A / (L ^ B * L ^ 3) := by positivity
  calc (k : ℝ) * (|C| * A / (L ^ B * L ^ 3)) ≤ ((|K| + 1) * L) * (|C| * A / (L ^ B * L ^ 3)) :=
         mul_le_mul_of_nonneg_right hkL hx
       _ = (|K| + 1) * |C| * A / (L ^ B * L ^ 2) := by field_simp
       _ ≤ (|K| + 1) * |C| * A / L ^ B := by
         apply div_le_div_of_nonneg_left (by positivity) hLB
         exact le_mul_of_one_le_right hLB.le (one_le_pow₀ hL1)

#print axioms lemma17_uniform
#print axioms ceil_blocks_le
#print axioms lemma17_blocks_uniform_from_leaves
end
end LeanLab.Languasco2004.Feed578aBlocks17
