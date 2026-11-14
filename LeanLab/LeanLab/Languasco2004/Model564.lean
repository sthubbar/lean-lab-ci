/-
Jia 1996 pages 263 and 270 to 282, displays 48 and 52.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
These are arithmetic model data and elementary transfer steps.
-/
import LeanLab.Languasco2004.GroupSplit548
import LeanLab.Languasco2004.Numeric30_548

namespace LeanLab.Languasco2004.Model564
open Finset Real Decomp279a Decomp316a Decomp316c GroupSplit548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 263 display 48: the rough count S of B_d and z.
B is the interval Y less than a at most 2Y. Every prime below z is excluded. -/
def roughCount (Y : ℝ) (d : ℕ) (z : ℝ) : ℕ :=
  ((Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter (fun a => d ∣ a ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a)).card

/-- Pages 270 and 280: the arithmetic model for a finite family of source regions.
The finite cap 2Y omits only zero summands in the positive source domain. -/
def roughModel (labels : Finset ℕ) (Y : ℝ) : ℝ :=
  ∑ p ∈ range (⌊2 * Y⌋₊ + 1), ∑ q ∈ range (⌊2 * Y⌋₊ + 1),
    if p.Prime ∧ q.Prime ∧ regionIndex Y p q ∈ labels
      then (roughCount Y (p * q) q : ℝ) else 0

/-- Page 263 display 48: a divisor larger than 2Y contributes no rough integers. -/
theorem roughCount_zero_of_large_divisor (Y : ℝ) (d : ℕ) (z : ℝ)
    (_hY : 0 ≤ Y) (hd : ⌊2*Y⌋₊ < d) : roughCount Y d z = 0 := by
  unfold roughCount
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro a ha h
  obtain ⟨hal, hau⟩ := mem_Ioc.mp ha
  have ha0 : 0 < a := by omega
  have hda := Nat.le_of_dvd ha0 h.1
  omega

/-- Pages 270 and 280: the rough model prime caps omit only zero summands. -/
theorem rough_summand_zero_of_large_index (Y : ℝ) (p q : ℕ)
    (hY : 0 ≤ Y) (hp : p.Prime) (hq : q.Prime)
    (hlarge : ⌊2*Y⌋₊ < p ∨ ⌊2*Y⌋₊ < q) : roughCount Y (p*q) q = 0 := by
  apply roughCount_zero_of_large_divisor Y (p*q) q hY
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  rcases hlarge with h | h <;> nlinarith

/-- Page 280: the seven remaining regions supplied by Lemma 11.
The four contiguous middle regions form one integral domain. -/
def labels11 : Finset ℕ := {33, 36, 38, 40, 42, 46, 49}

/-- Pages 281 and 282: the two remaining regions supplied by Lemma 12. -/
def labels12 : Finset ℕ := {53, 66}

/-- Page 280: the remainder is the disjoint union of the two mean value families. -/
theorem remainder_labels :
    Disjoint labels11 labels12 ∧
      labels11 ∪ labels12 = ({33, 36, 38, 40, 42, 46, 49, 53, 66} : Finset ℕ) := by
  constructor
  · norm_num [labels11, labels12, disjoint_left]
  · ext k
    simp [labels11, labels12, or_left_comm]

/-- Page 263 display 48: every arithmetic model is nonnegative. -/
theorem roughModel_nonneg (labels : Finset ℕ) (Y : ℝ) : 0 ≤ roughModel labels Y := by
  unfold roughModel
  exact sum_nonneg fun p _ => sum_nonneg fun q _ => by split_ifs <;> positivity

/-- Page 280: disjoint source region families have additive arithmetic models. -/
theorem roughModel_union (s t : Finset ℕ) (h : Disjoint s t) (Y : ℝ) :
    roughModel (s ∪ t) Y = roughModel s Y + roughModel t Y := by
  unfold roughModel
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

/-- Page 208: every positive localization exponent eventually exceeds a fixed Y threshold. -/
theorem localization_large (ε L : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → 2 ≤ N ∧ max 2 L ≤ localization N ε := by
  obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp
    (_root_.tendsto_rpow_atTop (by linarith : (0 : ℝ) < 7 / 12 + ε)) (max 2 L)
  exact ⟨max M 2, fun N hN => ⟨(le_max_right _ _).trans hN,
    hM N ((le_max_left _ _).trans hN)⟩⟩

/-- Pages 270 and 280: multiplication by the singular factor transfers a model lower bound. -/
theorem model_scale_lower (labels : Finset ℕ) (N Y a : ℝ) (n : ℕ)
    (hN : 2 ≤ N) (hmodel : a * Y / Real.log Y ≤ roughModel labels Y) :
    a * scale N Y n ≤ singular n / Real.log N * roughModel labels Y := by
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 ≤ singular n / Real.log N := div_nonneg (singular_nonneg n) hlog.le
  have h := mul_le_mul_of_nonneg_left hmodel hpos
  convert h using 1
  unfold scale
  ring

/-- Pages 270 and 280: a finite failure set shrinks when the model clears a reserve. -/
theorem bad_transfer (w : Finset ℕ) (f m g : ℕ → ℝ) (a δ : ℝ)
    (hg : ∀ n ∈ w, (a + δ) * m n ≤ g n) :
    w.filter (fun n => f n < a * m n) ⊆
      w.filter (fun n => f n + δ * m n < g n) := by
  intro n hn
  obtain ⟨hw, hf⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hw, by nlinarith [hg n hw]⟩

/-- Page 280: the clipped prime count over a finite family of source regions. -/
def primeModel (labels : Finset ℕ) (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
    ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))),
      if regionIndex Y p q ∈ labels then (sifted N Y n (p*q) q : ℝ) else 0

/-- Page 280: the two source mean value families partition the clipped remainder. -/
theorem primeModel_remainder (N Y : ℝ) (n : ℕ) :
    primeModel labels11 N Y n + primeModel labels12 N Y n = pieceSum 4 30 false N Y n := by
  unfold primeModel pieceSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have he (k : ℕ) : (groupOf k = 4 ∧ decide (k = 30) = false) ↔
      k ∈ labels11 ∪ labels12 := by
    simp only [groupOf, labels11, labels12, mem_insert, mem_singleton, mem_union,
      decide_eq_false_iff_not]
    split_ifs <;> simp_all <;> omega
  have hd : ¬ (regionIndex Y p q ∈ labels11 ∧ regionIndex Y p q ∈ labels12) :=
    fun hh => (disjoint_left.mp remainder_labels.1) hh.1 hh.2
  by_cases h11 : regionIndex Y p q ∈ labels11 <;>
    by_cases h12 : regionIndex Y p q ∈ labels12 <;>
    simp_all

/-- Pages 270 and 280: abstract finite assembly of the two source transfers.
CONDITIONAL ON the supplied prime comparison and arithmetic model evaluation.
The proof itself has only the standard axioms. -/
theorem lower_from_model (f : ℝ → ℝ → ℕ → ℝ) (labels : Finset ℕ) (I a : ℝ)
    (hI : a < I)
    (hprime : ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n => f N (localization N ε) n +
          δ * scale N (localization N ε) n < singular n / Real.log N *
          roughModel labels (localization N ε))).card : ℝ) ≤
          C * windowLength N ε / Real.log N ^ B)
    (hmodel : ∀ δ : ℝ, 0 < δ → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      (I - δ) * Y / Real.log Y ≤ roughModel labels Y) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => f N (localization N ε) n <
        a * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  let δ := (I-a)/3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨e, he, hprime⟩ := hprime δ hδ
  obtain ⟨Y₀, hmodel⟩ := hmodel δ hδ
  refine ⟨e, he, ?_⟩
  intro ε B hε he' hB
  obtain ⟨C, M, hC⟩ := hprime ε B hε he' hB
  obtain ⟨L, hL⟩ := localization_large ε Y₀ hε
  refine ⟨C, max M L, ?_⟩
  intro N hN
  obtain ⟨hN2, hY⟩ := hL N ((le_max_right _ _).trans hN)
  have hY2 : 2 ≤ localization N ε := (le_max_left _ _).trans hY
  have hYM : Y₀ ≤ localization N ε := (le_max_right _ _).trans hY
  have hlog : 0 ≤ Real.log (localization N ε) := Real.log_nonneg (by linarith)
  have hcoeff : a + δ ≤ I - δ := by dsimp [δ]; linarith
  have hmod : (a + δ) * localization N ε / Real.log (localization N ε) ≤
      roughModel labels (localization N ε) :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (by linarith)) hlog).trans (hmodel _ hYM hY2)
  have hs := bad_transfer (window N ε)
    (f N (localization N ε)) (scale N (localization N ε))
    (fun n => singular n / Real.log N * roughModel labels (localization N ε)) a δ
    (fun n _ => model_scale_lower labels N (localization N ε) (a+δ) n hN2 hmod)
  have hc : (((window N ε).filter (fun n => f N (localization N ε) n <
      a * scale N (localization N ε) n)).card : ℝ) ≤
      (((window N ε).filter (fun n => f N (localization N ε) n +
        δ * scale N (localization N ε) n < singular n / Real.log N *
        roughModel labels (localization N ε))).card : ℝ) := by
    exact_mod_cast card_le_card hs
  exact hc.trans (hC N ((le_max_left _ _).trans hN))

#print axioms primeModel_remainder
#print axioms lower_from_model
#print axioms roughCount_zero_of_large_divisor
#print axioms rough_summand_zero_of_large_index
#print axioms remainder_labels
#print axioms roughModel_nonneg
#print axioms roughModel_union
#print axioms localization_large
#print axioms model_scale_lower
#print axioms bad_transfer
end
end LeanLab.Languasco2004.Model564
