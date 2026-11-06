/-
P0093 page 163 binary runs. Bridge to the proved Gallagher binary change count.
P0094 pages 132 and 133 give the later proof of the same counting argument.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp412c
import LeanLab.Linnik.Gallagher1975Lemma2

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 163 after equation 7.12. A near integer doubling at
binary radius at most one sixteenth forces two adjacent binary digits
 to agree. Reuse the proved lab cosine to digit implication from P0094
page 132 Lemma 1. -/
theorem near_phase_digit_equal412 (M r m : ℕ) (hr : 4 ≤ r) (α : ℝ)
    (hm : m ∈ nearIntegerIndices412 M r α) :
    LeanLab.Linnik.Gallagher1975Lemma1.digit α (m + 2) =
      LeanLab.Linnik.Gallagher1975Lemma1.digit α (m + 3) := by
  classical
  obtain ⟨_, z, hz⟩ := Finset.mem_filter.mp hm
  have hrad : (1 / 2 : ℝ) ^ r ≤ 1 / 16 := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hr
    norm_num at h ⊢
    exact h
  have habs := abs_le.mp (hz.trans hrad)
  have harg : 2 * Real.pi * ((2 : ℝ) ^ (m + 1) * α - z) ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcos := Real.cos_pos_of_mem_Ioo harg
  have heq : 2 * Real.pi * ((2 : ℝ) ^ (m + 1) * α) =
      2 * Real.pi * ((2 : ℝ) ^ (m + 1) * α - z) + (z : ℝ) * (2 * Real.pi) := by ring
  have hp : 0 < Real.cos (2 * Real.pi * ((2 : ℝ) ^ (m + 1) * α)) := by
    rw [heq, Real.cos_add_int_mul_two_pi]
    exact hcos
  simpa only [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega] using
    LeanLab.Linnik.Gallagher1975Lemma1.digit_eq_of_cos_pos α (m + 1) hp

/-- P0093 page 164 binary run count leading to 7.13. Every change
in the interior digit string corresponds injectively to an index outside
the near integer set. This supplies the exact exceptional set needed
by the existing Gallagher finite word counting proof. -/
theorem changes_le_bad_indices412 (M r : ℕ) (hr : 4 ≤ r) (α : ℝ) :
    (LeanLab.Linnik.Gallagher1975Lemma1.changes α M).card ≤
      M - (nearIntegerIndices412 M r α).card := by
  classical
  have hc : (LeanLab.Linnik.Gallagher1975Lemma1.changes α M).card ≤
      ((range M) \ nearIntegerIndices412 M r α).card := by
    apply Finset.card_le_card_of_injOn (fun m : ℕ => m - 2)
    · intro m hm
      have hmem := Finset.mem_filter.mp hm
      have hb := Finset.mem_Icc.mp hmem.1
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_range.mpr (by change m - 2 < M; omega), ?_⟩
      intro hnear
      have heq := near_phase_digit_equal412 M r (m - 2) hr α hnear
      have h1 : m - 2 + 2 = m := by omega
      have h2 : m - 2 + 3 = m + 1 := by omega
      rw [h1, h2] at heq
      exact hmem.2 heq
    · intro m hm n hn hmn
      have hm2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
      have hn2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      change m - 2 = n - 2 at hmn
      omega
  have hs : nearIntegerIndices412 M r α ⊆ range M := Finset.filter_subset _ _
  simpa only [Finset.card_sdiff_of_subset hs, Finset.card_range] using hc

/-- P0093 page 164 equations 7.13 through 7.15. The concentration
fraction implies the corresponding real upper bound for digit changes.
The existing Gallagher count and binomial estimate can now be reused. -/
theorem changes_fraction_bound412 (M r : ℕ) (hr : 4 ≤ r) (α ε : ℝ)
    (hgood : (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card) :
    ((LeanLab.Linnik.Gallagher1975Lemma1.changes α M).card : ℝ) ≤ ε * M := by
  classical
  have hc := changes_le_bad_indices412 M r hr α
  have hs : (nearIntegerIndices412 M r α).card ≤ M := by
    simpa only [nearIntegerIndices412, Finset.card_range] using Finset.card_filter_le
      (s := range M) (p := fun m => ∃ z : ℤ, |α * (2 : ℝ) ^ (m + 1) - z| ≤ (1 / 2 : ℝ) ^ r)
  have hR : ((LeanLab.Linnik.Gallagher1975Lemma1.changes α M).card : ℝ) ≤
      (M : ℝ) - (nearIntegerIndices412 M r α).card := by
    exact_mod_cast hc
  linarith

/-- P0093 page 164 equation 7.13 and page 165 equation 7.19.
The binary word of a concentrated phase belongs to the exact finite
word set already counted in the proved Gallagher module. -/
theorem concentrated_word_mem412 (M r : ℕ) (hr : 4 ≤ r) (α ε : ℝ)
    (hα : α ∈ Set.Ico 0 1)
    (hgood : (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card) :
    ⌊(2 : ℝ) ^ (M + 1) * α⌋₊ ∈ LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, ?_⟩
  · have hfloor := Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (M + 1)) hα.1)
    have hn : (⌊(2 : ℝ) ^ (M + 1) * α⌋₊ : ℝ) < (2 : ℝ) ^ (M + 1) := by
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (M + 1), hα.2]
    exact_mod_cast hn
  · rw [← LeanLab.Linnik.Gallagher1975Lemma1.changes_eq_bitChanges hα.1]
    have h := changes_fraction_bound412 M r hr α ε hgood
    convert h using 1 <;> ring

/-- P0093 page 165 after equation 7.19. A finite collection of binary
words covers its phases by equal dyadic cells. Its measure is at most
the word count times their common length. -/
theorem binary_cells_measure412 (M : ℕ) (S : Finset ℕ) :
    MeasureTheory.volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      ⌊(2 : ℝ) ^ (M + 1) * α⌋₊ ∈ S} ≤
        (S.card : ENNReal) * ENNReal.ofReal (1 / (2 : ℝ) ^ (M + 1)) := by
  classical
  have hsub : {α : ℝ | α ∈ Set.Ico 0 1 ∧ ⌊(2 : ℝ) ^ (M + 1) * α⌋₊ ∈ S} ⊆
      ⋃ n ∈ S, Set.Ico ((n : ℝ) / 2 ^ (M + 1)) (((n : ℝ) + 1) / 2 ^ (M + 1)) := by
    intro α hα
    let n := ⌊(2 : ℝ) ^ (M + 1) * α⌋₊
    have hnlo : (n : ℝ) ≤ 2 ^ (M + 1) * α := Nat.floor_le (mul_nonneg (by positivity) hα.1.1)
    have hnhi : (2 : ℝ) ^ (M + 1) * α < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    refine Set.mem_iUnion₂.mpr ⟨n, hα.2, ?_, ?_⟩
    · exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (M + 1))).mpr (by nlinarith)
    · exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (M + 1))).mpr (by nlinarith)
  calc
    _ ≤ MeasureTheory.volume (⋃ n ∈ S,
        Set.Ico ((n : ℝ) / 2 ^ (M + 1)) (((n : ℝ) + 1) / 2 ^ (M + 1))) :=
      MeasureTheory.measure_mono hsub
    _ ≤ ∑ n ∈ S, MeasureTheory.volume
        (Set.Ico ((n : ℝ) / 2 ^ (M + 1)) (((n : ℝ) + 1) / 2 ^ (M + 1))) :=
      MeasureTheory.measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [Real.volume_Ico]
      have he (n : ℕ) : ((n : ℝ) + 1) / 2 ^ (M + 1) - (n : ℝ) / 2 ^ (M + 1) =
          1 / 2 ^ (M + 1) := by ring
      simp only [he, Finset.sum_const, nsmul_eq_mul]

/-- P0093 page 164 word count and page 165 conversion to measure.
The actual near integer phase set in one period is bounded by the
proved Gallagher word count at parameter epsilon over four. -/
theorem binary_unit_measure_le_words412 (M r : ℕ) (hr : 4 ≤ r) (ε : ℝ) :
    MeasureTheory.volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≤
        ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ENNReal) *
          ENNReal.ofReal (1 / (2 : ℝ) ^ (M + 1)) := by
  apply le_trans (MeasureTheory.measure_mono (t := {α : ℝ | α ∈ Set.Ico 0 1 ∧
    ⌊(2 : ℝ) ^ (M + 1) * α⌋₊ ∈ LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)}) ?_)
    (binary_cells_measure412 M _)
  intro α hα
  exact ⟨hα.1, concentrated_word_mem412 M r hr α ε hα.1 hα.2⟩

/-- P0093 page 163 binary expansion and page 165 measure bound.
Integer translation preserves the exact near integer index set.
Thus the binary concentration condition is periodic with period one. -/
theorem near_indices_int_shift412 (M r : ℕ) (α : ℝ) (z : ℤ) :
    nearIntegerIndices412 M r (α + z) = nearIntegerIndices412 M r α := by
  classical
  ext m
  simp only [nearIntegerIndices412, Finset.mem_filter]
  apply and_congr_right
  intro hm
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - z * 2 ^ (m + 1), ?_⟩
    have he : α * (2 : ℝ) ^ (m + 1) - ((k - z * 2 ^ (m + 1) : ℤ) : ℝ) =
        (α + z) * (2 : ℝ) ^ (m + 1) - k := by push_cast; ring
    rw [he]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k + z * 2 ^ (m + 1), ?_⟩
    have he : (α + z) * (2 : ℝ) ^ (m + 1) - ((k + z * 2 ^ (m + 1) : ℤ) : ℝ) =
        α * (2 : ℝ) ^ (m + 1) - k := by push_cast; ring
    rw [he]
    exact hk

/-- P0093 page 164 binomial estimate 7.15 and Gallagher page 133
counting proof. Reuse the proved finite word injection and small subset
bound to retain the explicit entropy expression before choosing epsilon. -/
theorem binary_word_card_bound412 (M : ℕ) (ε : ℝ)
    (hε : 0 < ε * M) (hM : ε * M ≤ (M - 1 : ℕ)) :
    ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ℝ) ≤
      4 * (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M) := by
  classical
  have he : 4 * (ε / 4) * (M : ℝ) = ε * M := by ring
  have hc := LeanLab.Linnik.Gallagher1975Lemma1.card_T_le M (ε / 4)
  rw [he] at hc
  have hcard : (Icc 2 M).card = M - 1 := by simp
  have hs := LeanLab.Linnik.Gallagher1975Lemma1.card_small_subsets_le
    (Icc 2 M) hε (by simpa only [hcard] using hM)
  rw [hcard] at hs
  have hcR : ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ℝ) ≤
      4 * ({S ∈ (Icc 2 M).powerset | (S.card : ℝ) ≤ ε * M}.card : ℝ) := by
    exact_mod_cast hc
  exact hcR.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

/-- P0093 page 165 conversion of word count to measure after 7.19.
The actual binary concentration set in one period satisfies the explicit
binomial entropy bound already proved in the Gallagher counting library.
Only the small fraction choice and bounded period extension remain. -/
theorem binary_unit_measure_explicit412 (M r : ℕ) (hr : 4 ≤ r) (ε : ℝ)
    (hε : 0 < ε * M) (hM : ε * M ≤ (M - 1 : ℕ)) :
    MeasureTheory.volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≤
        ENNReal.ofReal (4 * (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M) /
          (2 : ℝ) ^ (M + 1)) := by
  have hc := binary_word_card_bound412 M ε hε hM
  have hcE : ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ENNReal) ≤
      ENNReal.ofReal (4 * (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hc
  calc
    _ ≤ ((LeanLab.Linnik.Gallagher1975Lemma1.T M (ε / 4)).card : ENNReal) *
        ENNReal.ofReal (1 / (2 : ℝ) ^ (M + 1)) := binary_unit_measure_le_words412 M r hr ε
    _ ≤ ENNReal.ofReal (4 * (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M)) *
        ENNReal.ofReal (1 / (2 : ℝ) ^ (M + 1)) := mul_le_mul_left hcE _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end LeanLab.Linnik1951
