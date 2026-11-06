/-
P0069, page 12, the logarithmic coefficient energy used in 3.10.
This file proves the branch with divisor exponent at most one half.
The unrestricted EnergyLogBound input remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp386b

namespace LeanLab.BHP1997.Decomp414c
open Classical MeanSquareC165
open scoped BigOperators

/-- Page 12, an auxiliary energy bound for divisor exponent at most one half.
The coefficient square is bounded by tau, and the first divisor moment
is supplied by the proved Decomp386b.divisor_sum_bound. -/
theorem energy_le_log_of_half {a : ℕ → ℂ} {B c1 c2 F : ℝ}
    (hB : B ≤ 1 / 2) (ha : Thm4.CoeffBound a B)
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hF : 2 ≤ F) :
    energy a c1 c2 F ≤ (c2 / c1) * (1 + |Real.log c2| + Real.log F) := by
  let N := ⌊c2 * F⌋₊
  let S := (Finset.range (N + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  have hF0 : 0 < F := by linarith
  have hlogF : 0 ≤ Real.log F := Real.log_nonneg (by linarith)
  have hden : 0 < c1 * F := mul_pos hc1 hF0
  have hsub : S ⊆ Finset.Ioc 0 N := by
    intro n hn
    obtain ⟨hnN, hnlo, hnhi⟩ := Finset.mem_filter.mp hn
    have hn0 : 0 < (n : ℝ) := hden.trans hnlo
    rw [Finset.mem_range] at hnN
    exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hn0, by omega⟩
  change (∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ)) ≤ _
  by_cases hN : N = 0
  · have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hh := hsub hn
      simp [hN] at hh
    rw [he, Finset.sum_empty]
    positivity
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
  have hNle : (N : ℝ) ≤ c2 * F := Nat.floor_le (mul_pos hc2 hF0).le
  have hlogN : Real.log (N : ℝ) ≤ Real.log c2 + Real.log F := by
    have hh := Real.log_le_log hN0 hNle
    rwa [Real.log_mul (ne_of_gt hc2) (ne_of_gt hF0)] at hh
  have hbudget : 0 ≤ 1 + |Real.log c2| + Real.log F := by positivity
  have hNb : (N : ℝ) * (1 + Real.log N) ≤
      c2 * F * (1 + |Real.log c2| + Real.log F) := by
    exact mul_le_mul hNle (by linarith [le_abs_self (Real.log c2)])
      (by linarith [Real.log_nonneg hN1]) (mul_pos hc2 hF0).le
  calc
    _ ≤ ∑ n ∈ S, (n.divisors.card : ℝ) / (c1 * F) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnlo := (Finset.mem_filter.mp hn).2.1
      have hn0 : n ≠ 0 := by
        intro he
        subst n
        norm_num at hnlo
        linarith
      have ht : 1 ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
      have hsq : ‖a n‖ ^ 2 ≤ (n.divisors.card : ℝ) := by
        calc
          _ ≤ ((n.divisors.card : ℝ) ^ B) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (ha n) 2
          _ = (n.divisors.card : ℝ) ^ (B * (2 : ℕ)) :=
            (Real.rpow_mul_natCast (by positivity) B 2).symm
          _ ≤ (n.divisors.card : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ht (by norm_num only [Nat.cast_ofNat]; linarith)
          _ = _ := Real.rpow_one _
      exact (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg _)).trans
        (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden hnlo.le)
    _ = (∑ n ∈ S, (n.divisors.card : ℝ)) / (c1 * F) := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ)) / (c1 * F) :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnS => Nat.cast_nonneg _)) hden.le
    _ ≤ ((N : ℝ) * (1 + Real.log N)) / (c1 * F) :=
      div_le_div_of_nonneg_right (Decomp386b.divisor_sum_bound N) hden.le
    _ ≤ (c2 * F * (1 + |Real.log c2| + Real.log F)) / (c1 * F) :=
      div_le_div_of_nonneg_right hNb hden.le
    _ = _ := by field_simp [ne_of_gt hc1, ne_of_gt hF0]

/-- Page 12, the fixed-B logarithmic energy input is proved for every B at most one half.
This is a partial branch, not a proof of the unrestricted EnergyLogBound Prop. -/
theorem energy_log_bound_of_half (B : ℝ) (hB : B ≤ 1 / 2) :
    ∀ c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ K C : ℝ, 0 < C ∧
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B → ∀ F : ℝ, 2 ≤ F →
        energy a c1 c2 F ≤ C * Real.log F ^ K := by
  intro c1 c2 hc1 hc2
  have hc2p : 0 < c2 := hc1.trans hc2
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let R : ℝ := (1 + |Real.log c2|) / Real.log 2 + 1
  let C : ℝ := (c2 / c1) * R
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨1, C, mul_pos (div_pos hc2p hc1) hR, ?_⟩
  intro a ha F hF
  have hlog : Real.log 2 ≤ Real.log F := Real.log_le_log (by norm_num) hF
  have hscale := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (1 + |Real.log c2|) / Real.log 2 by positivity)
  have hid : (1 + |Real.log c2|) / Real.log 2 * Real.log 2 = 1 + |Real.log c2| :=
    div_mul_cancel₀ _ (ne_of_gt hl2)
  have hbudget : 1 + |Real.log c2| + Real.log F ≤ R * Real.log F := by
    dsimp [R]
    rw [hid] at hscale
    nlinarith
  calc
    _ ≤ (c2 / c1) * (1 + |Real.log c2| + Real.log F) :=
      energy_le_log_of_half hB ha hc1 hc2p hF
    _ ≤ (c2 / c1) * (R * Real.log F) :=
      mul_le_mul_of_nonneg_left hbudget (div_pos hc2p hc1).le
    _ = _ := by dsimp [C]; rw [Real.rpow_one]; ring

/-- Page 12, nonzero consistency instance for the positive half-exponent branch.
At F equal to 2, the energy support is the two integers 2 and 3. -/
theorem energy_half_instance :
    Thm4.CoeffBound (fun n => if n = 0 then 0 else 1) (1 / 2) ∧
      energy (fun n => if n = 0 then 0 else 1) (1 / 2) 2 2 = 5 / 6 := by
  constructor
  · intro n
    by_cases hn : n = 0
    · subst n
      simp
    · simp only [hn, ite_false, norm_one]
      apply Real.one_le_rpow _ (by norm_num)
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  · norm_num [energy, Finset.sum_filter, Finset.sum_range_succ]

end LeanLab.BHP1997.Decomp414c
