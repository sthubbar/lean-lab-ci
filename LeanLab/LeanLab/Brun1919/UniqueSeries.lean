/-
AI-written Lean code, Codex task05, 2026-10-22.
Convergence with each twin-prime denominator counted only once.
This audits the series convention in Brun's title, reproduced by Teissier
on printed p. 11-09. The original 1919 scan remains inaccessible.
-/
import LeanLab.Brun1919.TitleSeries

noncomputable section
namespace LeanLab.Brun1919

/-- Two adjacent twin pairs can overlap only in the prime triple 3, 5, 7. -/
lemma overlapping_twin_pairs_start (p : ℕ) (hp : IsTwin p) (hq : IsTwin (p + 2)) : p = 3 := by
  have hpp := hp.1.two_le
  have hd : p % 3 = 0 ∨ (p + 2) % 3 = 0 ∨ (p + 4) % 3 = 0 := by omega
  rcases hd with hd | hd | hd
  · have hh := (Nat.dvd_prime hp.1).mp (Nat.dvd_of_mod_eq_zero hd)
    omega
  · have hh := (Nat.dvd_prime hp.2).mp (Nat.dvd_of_mod_eq_zero hd)
    omega
  · have hprime : (p + 4).Prime := by convert hq.2 using 1 <;> omega
    have hh := (Nat.dvd_prime hprime).mp (Nat.dvd_of_mod_eq_zero hd)
    omega

/-- The reciprocal series over the larger twin member is summable. -/
lemma brun_larger : Summable (fun p : ℕ => if IsTwin p then (1 : ℝ) / (p + 2) else 0) := by
  refine Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) ?_ brun
  intro p
  split_ifs
  · have h : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith
  · exact le_rfl

/-- Larger-member reciprocals, indexed by their actual denominators. -/
lemma brun_larger_shifted : Summable (fun q : ℕ =>
    if 2 ≤ q ∧ IsTwin (q - 2) then (1 : ℝ) / q else 0) := by
  apply (summable_nat_add_iff 2).mp
  convert brun_larger using 1
  ext p
  have hp2 : 2 ≤ p + 2 := by omega
  simp [hp2]

/-- The reciprocal sum over the union of both twin-member sets converges, counting each once. -/
theorem brun_unique : Summable (fun q : ℕ =>
    if IsTwin q ∨ (2 ≤ q ∧ IsTwin (q - 2)) then (1 : ℝ) / q else 0) := by
  refine Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity) ?_
    (brun_smaller.add brun_larger_shifted)
  intro q
  change (if IsTwin q ∨ (2 ≤ q ∧ IsTwin (q - 2)) then (1 : ℝ) / q else 0) ≤
    (if IsTwin q then (1 : ℝ) / q else 0) +
      (if 2 ≤ q ∧ IsTwin (q - 2) then (1 : ℝ) / q else 0)
  by_cases hs : IsTwin q <;> by_cases hl : 2 ≤ q ∧ IsTwin (q - 2) <;>
    simp [hs, hl] <;> positivity

/-- The union predicate is exactly primality with a prime neighbor at distance two. -/
lemma unique_twin_iff_prime_neighbor (q : ℕ) :
    (IsTwin q ∨ (2 ≤ q ∧ IsTwin (q - 2))) ↔
      (q.Prime ∧ ((q + 2).Prime ∨ (q - 2).Prime)) := by
  constructor
  · rintro (hs | ⟨hq2, hp, hq⟩)
    · exact ⟨hs.1, Or.inl hs.2⟩
    · exact ⟨by simpa [Nat.sub_add_cancel hq2] using hq, Or.inr hp⟩
  · rintro ⟨hq, hn | hp⟩
    · exact Or.inl ⟨hq, hn⟩
    · refine Or.inr ⟨hq.two_le, hp, ?_⟩
      simpa [Nat.sub_add_cancel hq.two_le] using hq

/-- Brun convergence with each prime having a prime neighbor at distance two counted once. -/
theorem brun_unique_prime_neighbor : Summable (fun q : ℕ =>
    if q.Prime ∧ ((q + 2).Prime ∨ (q - 2).Prime) then (1 : ℝ) / q else 0) := by
  simpa only [unique_twin_iff_prime_neighbor] using brun_unique

/-- A denominator is both a smaller and a larger twin member exactly when it is five. -/
lemma twin_denominator_overlap_iff (q : ℕ) :
    (IsTwin q ∧ (2 ≤ q ∧ IsTwin (q - 2))) ↔ q = 5 := by
  constructor
  · rintro ⟨hq, hq2, hp⟩
    have hn : IsTwin (q - 2 + 2) := by simpa [Nat.sub_add_cancel hq2] using hq
    have hstart := overlapping_twin_pairs_start (q - 2) hp hn
    omega
  · rintro rfl
    norm_num [IsTwin]

/-- Counting each denominator once removes exactly one copy of the reciprocal of five. -/
lemma unique_denominator_term_correction (q : ℕ) :
    (if IsTwin q then (1 : ℝ) / q else 0) +
      (if 2 ≤ q ∧ IsTwin (q - 2) then (1 : ℝ) / q else 0) =
        (if IsTwin q ∨ (2 ≤ q ∧ IsTwin (q - 2)) then (1 : ℝ) / q else 0) +
          (if q = 5 then (1 / 5 : ℝ) else 0) := by
  by_cases hs : IsTwin q
  · by_cases hl : 2 ≤ q ∧ IsTwin (q - 2)
    · have hq := (twin_denominator_overlap_iff q).mp ⟨hs, hl⟩
      subst q
      norm_num [IsTwin]
    · have hq : q ≠ 5 := by rintro rfl; norm_num [IsTwin] at hl
      simp [hs, hl, hq]
  · have hq : q ≠ 5 := by rintro rfl; norm_num [IsTwin] at hs
    by_cases hl : 2 ≤ q ∧ IsTwin (q - 2) <;> simp [hs, hl, hq]

/-- Reindexing the larger members preserves their total reciprocal sum. -/
lemma brun_larger_tsum_shift :
    (∑' q : ℕ, if 2 ≤ q ∧ IsTwin (q - 2) then (1 : ℝ) / q else 0) =
      ∑' p : ℕ, if IsTwin p then (1 : ℝ) / (p + 2) else 0 := by
  have h := brun_larger_shifted.sum_add_tsum_nat_add 2
  have hprefix : (∑ q ∈ Finset.range 2,
      if 2 ≤ q ∧ IsTwin (q - 2) then (1 : ℝ) / q else 0) = 0 := by
    norm_num [Finset.range_add_one]
  rw [hprefix, zero_add] at h
  calc
    _ = ∑' q : ℕ, if 2 ≤ q + 2 ∧ IsTwin (q + 2 - 2) then
        (1 : ℝ) / ((q + 2 : ℕ) : ℝ) else 0 := h.symm
    _ = _ := by
      apply tsum_congr
      intro p
      have hp2 : 2 ≤ p + 2 := by omega
      simp [hp2]

/-- The full pair sum exceeds the unique-denominator sum by exactly 1/5. -/
theorem brun_unique_sum_difference :
    (∑' p : ℕ, if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) =
      (∑' q : ℕ, if IsTwin q ∨ (2 ≤ q ∧ IsTwin (q - 2)) then (1 : ℝ) / q else 0) +
        1 / 5 := by
  have hcombine :
      (∑' p : ℕ, if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) =
        (∑' p : ℕ, if IsTwin p then (1 : ℝ) / p else 0) +
          ∑' p : ℕ, if IsTwin p then (1 : ℝ) / (p + 2) else 0 := by
    rw [← brun_smaller.tsum_add brun_larger]
    apply tsum_congr
    intro p
    split_ifs <;> simp
  calc
    _ = (∑' p : ℕ, if IsTwin p then (1 : ℝ) / p else 0) +
        ∑' p : ℕ, if IsTwin p then (1 : ℝ) / (p + 2) else 0 := hcombine
    _ = (∑' p : ℕ, if IsTwin p then (1 : ℝ) / p else 0) +
        ∑' q : ℕ, if 2 ≤ q ∧ IsTwin (q - 2) then (1 : ℝ) / q else 0 := by
      rw [brun_larger_tsum_shift]
    _ = ∑' q : ℕ, ((if IsTwin q then (1 : ℝ) / q else 0) +
        (if 2 ≤ q ∧ IsTwin (q - 2) then (1 : ℝ) / q else 0)) :=
      (brun_smaller.tsum_add brun_larger_shifted).symm
    _ = ∑' q : ℕ, ((if IsTwin q ∨ (2 ≤ q ∧ IsTwin (q - 2)) then (1 : ℝ) / q else 0) +
        (if q = 5 then (1 / 5 : ℝ) else 0)) := tsum_congr unique_denominator_term_correction
    _ = _ := by
      rw [brun_unique.tsum_add (hasSum_ite_eq (5 : ℕ) (1 / 5 : ℝ)).summable]
      simp

#print axioms brun_unique_sum_difference

#print axioms brun_larger_tsum_shift

#print axioms unique_denominator_term_correction

#print axioms twin_denominator_overlap_iff

#print axioms brun_unique_prime_neighbor

#print axioms unique_twin_iff_prime_neighbor

#print axioms brun_unique

#print axioms brun_larger_shifted

#print axioms brun_larger

#print axioms overlapping_twin_pairs_start

end LeanLab.Brun1919
