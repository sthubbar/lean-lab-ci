/-
Jia 1996, Lemma 23, pages 265 to 267.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The two analytic estimates remain OPEN. The sealed leaf is not changed.
-/
import LeanLab.Languasco2004.Decomp316a

namespace LeanLab.Languasco2004.Decomp316b
open Finset Real Decomp279a Decomp316a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 265: the primes indexing the single subtraction. -/
def outerPrimes (Y : ℝ) (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y))

/-- Pages 265 and 266: the same outer sum at the lower sieve cutoff. -/
def lowSubtraction (N Y : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ outerPrimes Y n, (sifted N Y n p (Y ^ delta ε) : ℝ)

/-- Page 265 Buchstab subtraction before summing by the least offending q.
Count integers passing cutoff z but removed by cutoff Z. The existential
condition makes the endpoint convention explicit. -/
def deleted (N Y : ℝ) (n d : ℕ) (z Z : ℝ) : ℕ :=
  ((Icc 1 n).filter (fun a => d ∣ a ∧ (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
    (∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ a) ∧
    ∃ q : ℕ, q.Prime ∧ (q : ℝ) < Z ∧ ¬ q ∣ n ∧ q ∣ a)).card

/-- Pages 265 and 266: sum the terms removed between the two cutoffs. -/
def deletedSubtraction (N Y : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ outerPrimes Y n,
    (deleted N Y n p (Y ^ delta ε) (Y ^ (16 / 135 : ℝ)) : ℝ)

/-- Page 266: the leading coefficient of the low cutoff sum. -/
def lowCoefficient (ε : ℝ) : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) / delta ε * Real.log (135 / 32)

/-- Page 267: the upper Buchstab coefficient before rounding. -/
def upperCoefficient : ℝ := 0.5617 * (135 / 16) * Real.log (135 / 32)

/-- Page 265: partition a sifted set according to the higher cutoff. -/
theorem sifted_cutoff_partition (N Y : ℝ) (n d : ℕ) (z Z : ℝ) (hz : z ≤ Z) :
    sifted N Y n d Z + deleted N Y n d z Z = sifted N Y n d z := by
  let s := (Icc 1 n).filter (fun a => d ∣ a ∧ (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ a)
  let P := fun a : ℕ => ∀ p : ℕ, p.Prime → (p : ℝ) < Z → ¬ p ∣ n → ¬ p ∣ a
  have hhigh : s.filter P = (Icc 1 n).filter (fun a => d ∣ a ∧ (n - a).Prime ∧
      N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧ P a) := by
    ext a
    simp only [s, mem_filter]
    constructor
    · rintro ⟨⟨ha, hd, hp, hl, hu, _⟩, hP⟩
      exact ⟨ha, hd, hp, hl, hu, hP⟩
    · rintro ⟨ha, hd, hp, hl, hu, hP⟩
      exact ⟨⟨ha, hd, hp, hl, hu, fun p hp hpz => hP p hp (hpz.trans_le hz)⟩, hP⟩
  have hlow : (s.filter (fun a => ¬ P a)).card = deleted N Y n d z Z := by
    congr 1
    ext a
    simp only [s, P, deleted, mem_filter, not_forall, not_imp, not_not, and_assoc, exists_prop]
  have h := card_filter_add_card_filter_not (s := s) P
  rw [hhigh, hlow] at h
  exact h

/-- Page 265: summing the finite partitions gives the exact subtraction identity. -/
theorem subtraction_partition (N Y : ℝ) (n : ℕ) (ε : ℝ)
    (hz : Y ^ delta ε ≤ Y ^ (16 / 135 : ℝ)) :
    subtraction N Y n + deletedSubtraction N Y n ε = lowSubtraction N Y n ε := by
  unfold subtraction deletedSubtraction lowSubtraction outerPrimes
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  exact_mod_cast sifted_cutoff_partition N Y n p _ _ hz

/-- Page 267: the printed coefficient has room for two errors of 0.0000001. -/
theorem upperCoefficient_slack : upperCoefficient + 0.0000002 ≤ 6.822470 := by
  have hl : Real.log ((135 : ℝ) / 32) ≤ 1.4395389 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.4395389) 18
    have hs : (135 : ℝ) / 32 ≤ ∑ i ∈ range 18, (1.4395389 : ℝ) ^ i / Nat.factorial i := by
      norm_num [Finset.sum_range_succ]
    exact hs.trans h
  unfold upperCoefficient
  linarith

/-- LEAF. Page 266 first display, from Lemma 17 and the linear sieve.
Only the lower cutoff outer sum is bounded. -/
theorem low_subtraction_upper :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => (lowCoefficient ε + 0.0000001) *
        scale N (localization N ε) n < lowSubtraction N (localization N ε) n ε)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Page 266 remaining displays and page 267 first display.
Only the integers removed between the low and high cutoffs are bounded.
The least prime decomposition gives the paper's double sum. -/
theorem deleted_subtraction_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => deletedSubtraction N (localization N ε) n ε <
        (lowCoefficient ε - upperCoefficient - 0.0000001) *
          scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Page 208: a concrete epsilon cap puts delta below the main sieve exponent. -/
theorem delta_le_tenth {ε : ℝ} (hε : 0 < ε) (he : ε < (1 / 10 : ℝ) ^ (3 : ℕ)) :
    delta ε ≤ 1 / 10 := by
  have h := Real.rpow_le_rpow hε.le he.le (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc delta ε ≤ ((1 / 10 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := h
       _ = 1 / 10 := by
         rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 10)]
         norm_num

/-- Page 267: the union of the two failure sets gives the sealed statement.
CONDITIONAL ON low_subtraction_upper and deleted_subtraction_lower. -/
theorem subtraction_bound_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        6.822470 * scale N (localization N ε) n < subtraction N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e₁, he₁, h₁⟩ := low_subtraction_upper
  obtain ⟨e₂, he₂, h₂⟩ := deleted_subtraction_lower
  refine ⟨min (min e₁ e₂) ((1 / 10) ^ (3 : ℕ)),
    lt_min (lt_min he₁ he₂) (by norm_num), ?_⟩
  intro ε B hε he hB
  have he₁' := he.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have he₂' := he.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ := delta_le_tenth hε (he.trans_le (min_le_right _ _))
  obtain ⟨C₁, N₁, hC₁⟩ := h₁ ε B hε he₁' hB
  obtain ⟨C₂, N₂, hC₂⟩ := h₂ ε B hε he₂' hB
  refine ⟨C₁ + C₂, max (max N₁ N₂) 2, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNY : 1 ≤ localization N ε :=
    Real.one_le_rpow (by linarith) (by positivity : (0 : ℝ) ≤ 7 / 12 + ε)
  have hz : (localization N ε) ^ delta ε ≤ (localization N ε) ^ (16 / 135 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNY (by linarith)
  let bad₁ := (window N ε).filter (fun n => (lowCoefficient ε + 0.0000001) *
    scale N (localization N ε) n < lowSubtraction N (localization N ε) n ε)
  let bad₂ := (window N ε).filter (fun n => deletedSubtraction N (localization N ε) n ε <
    (lowCoefficient ε - upperCoefficient - 0.0000001) * scale N (localization N ε) n)
  have hsub : ((window N ε).filter (fun n =>
      6.822470 * scale N (localization N ε) n < subtraction N (localization N ε) n)) ⊆
        bad₁ ∪ bad₂ := by
    intro n hn
    obtain ⟨hnw, hbad⟩ := mem_filter.mp hn
    by_contra h
    have hlow : lowSubtraction N (localization N ε) n ε ≤
        (lowCoefficient ε + 0.0000001) * scale N (localization N ε) n := by
      apply le_of_not_gt
      intro hp
      exact h (mem_union_left _ (mem_filter.mpr ⟨hnw, hp⟩))
    have hdeleted : (lowCoefficient ε - upperCoefficient - 0.0000001) *
        scale N (localization N ε) n ≤ deletedSubtraction N (localization N ε) n ε := by
      apply le_of_not_gt
      intro hp
      exact h (mem_union_right _ (mem_filter.mpr ⟨hnw, hp⟩))
    have hs := scale_nonneg n (by linarith : 1 ≤ N) hNY
    have hc := subtraction_partition N (localization N ε) n ε hz
    have hk := mul_le_mul_of_nonneg_right upperCoefficient_slack hs
    nlinarith
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hcr : (((window N ε).filter (fun n =>
      6.822470 * scale N (localization N ε) n < subtraction N (localization N ε) n)).card : ℝ) ≤
        (bad₁.card : ℝ) + bad₂.card := by exact_mod_cast hc
  have hb := add_le_add (hC₁ N hN₁) (hC₂ N hN₂)
  calc _ ≤ (bad₁.card : ℝ) + bad₂.card := hcr
       _ ≤ C₁ * windowLength N ε / Real.log N ^ B +
           C₂ * windowLength N ε / Real.log N ^ B := hb
       _ = _ := by ring

#print axioms sifted_cutoff_partition
#print axioms subtraction_partition
#print axioms upperCoefficient_slack
#print axioms low_subtraction_upper
#print axioms deleted_subtraction_lower
#print axioms delta_le_tenth
#print axioms subtraction_bound_from_parts
end
end LeanLab.Languasco2004.Decomp316b
