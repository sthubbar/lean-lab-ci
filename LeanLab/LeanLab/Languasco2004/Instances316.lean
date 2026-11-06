/-
Concrete source instances for the task316 statements.
AI wrote the Lean code. Goldbach is open.
These validate statement domains and the printed partition.
-/
import LeanLab.Languasco2004.Decomp316b
import LeanLab.Languasco2004.Decomp316d
import LeanLab.Languasco2004.Geometry316
import LeanLab.Languasco2004.Instances279

namespace LeanLab.Languasco2004.Instances316
open Finset Real Decomp279a Decomp316a Decomp316b Decomp316c Decomp316d Geometry316
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 263 display 49: equal cutoffs remove no prime. -/
theorem removed_same (N Y z : ℝ) (n : ℕ) : removed N Y n z z = 0 := by
  unfold removed
  apply sum_eq_zero
  intro p hp
  obtain ⟨_, _, hpL, hpU⟩ := mem_filter.mp hp
  linarith

/-- Page 265: equal cutoffs delete no integer. -/
theorem deleted_same (N Y z : ℝ) (n d : ℕ) : deleted N Y n d z z = 0 := by
  unfold deleted
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro a _ h
  obtain ⟨_, _, _, _, hs, q, hq, hqz, hqn, hqa⟩ := h
  exact hs q hq hqz hqn hqa

/-- Concrete nonempty low cutoff instance from the existing source count. -/
theorem low_sieve_instance : lowSieve 3 2 4 0 = 2 := by
  simp [lowSieve, delta, Instances279.jia_sifted_instance]

/-- Empty finite cap instances for the three new sums. -/
theorem empty_cap_instances (N Y ε : ℝ) (j : ℕ) :
    lowSubtraction N Y 0 ε = 0 ∧ deletedSubtraction N Y 0 ε = 0 ∧ groupSum j N Y 0 = 0 := by
  have hp : outerPrimes Y 0 = ∅ := by
    unfold outerPrimes
    apply filter_eq_empty_iff.mpr
    intro p hpr h
    have : p = 0 := by have := mem_range.mp hpr; omega
    subst p
    exact (by decide : ¬ Nat.Prime 0) h.1
  refine ⟨?_, ?_, ?_⟩
  · rw [lowSubtraction, hp, sum_empty]
  · rw [deletedSubtraction, hp, sum_empty]
  · unfold groupSum
    change (∑ p ∈ outerPrimes Y 0, _) = 0
    rw [hp, sum_empty]

/-- One printed label in each of Lemmas 24 to 28. -/
theorem group_label_instances :
    groupOf 11 = 1 ∧ groupOf 47 = 2 ∧ groupOf 4 = 3 ∧ groupOf 30 = 4 ∧ groupOf 1 = 5 := by
  norm_num [groupOf]

/-- Pages 267 to 269: every printed label belongs to one of the five groups. -/
theorem every_label_assigned : ∀ i : Fin 69, 1 ≤ groupOf (i.val + 1) ∧ groupOf (i.val + 1) ≤ 5 := by
  decide +kernel

/-- A positive natural pair belongs to D_1. Primality is not a hypothesis
of the region assignment itself. The powers make all comparisons exact. -/
theorem region_one_instance : regionIndex ((2 : ℝ) ^ (135 : ℕ))
    ((2 : ℕ) ^ 20) ((2 : ℕ) ^ 18) = 1 := by
  apply regionIndex_eq_of_mem (⟨0, by decide⟩ : Fin 69)
  · norm_num
  · positivity
  · positivity
  · have hlow : ((2 : ℝ) ^ (135 : ℕ)) ^ (16 / 135 : ℝ) = (2 : ℝ) ^ (16 : ℕ) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hupper : (2 : ℝ) ^ (20 : ℕ) ≤ ((2 : ℝ) ^ (135 : ℕ)) ^ (89 / 462 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    norm_num [regionData, hlow] at hupper ⊢
    exact hupper

/-- Page 262 display 45: the first two lower product factors. -/
theorem prime_loss_instances :
    primeLoss (⟨3, by decide⟩ : Nat.Primes) = 1 / 4 ∧
    tailLoss (⟨2, by decide⟩ : Nat.Primes) = 0 ∧
    1 - tailLoss (⟨3, by decide⟩ : Nat.Primes) = 3 / 4 := by
  norm_num [primeLoss, tailLoss]

/-- Concrete explicit domain for the strengthened one sided extraction. -/
theorem prime_extraction_instance : sifted 10 2 12 1 (Real.sqrt 4) ≤ representations 10 2 12 + 1 := by
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
    prime_extraction 10 2 12 (by norm_num) (by norm_num)

/-- A concrete positive epsilon satisfies the conservative localization cap. -/
theorem localization_instance :
    1 < localization 64 (1 / 2000) ∧
      Real.sqrt (2 * localization 64 (1 / 2000)) ≤ 64 - localization 64 (1 / 2000) ∧
      windowLength 64 (1 / 2000) ≤ localization 64 (1 / 2000) :=
  localization_domain (by norm_num) (by norm_num) (by norm_num)

/-- The explicit error envelope also has a small domain instance. -/
theorem envelope_instance : errorEnvelope 1 ≤ 5 := by
  simpa using errorEnvelope_le (Y := 1) (by norm_num)

#print axioms removed_same
#print axioms deleted_same
#print axioms low_sieve_instance
#print axioms empty_cap_instances
#print axioms group_label_instances
#print axioms every_label_assigned
#print axioms region_one_instance
#print axioms prime_loss_instances
#print axioms prime_extraction_instance
#print axioms localization_instance
#print axioms envelope_instance
end
end LeanLab.Languasco2004.Instances316
