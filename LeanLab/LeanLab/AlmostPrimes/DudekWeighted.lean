import Mathlib

/-!
# Dudek's weighted square-free representation criterion

AI wrote the Lean code. Goldbach is open.
Dudek, On the Sum of a Prime and a Square-free Number,
https://arxiv.org/abs/1410.7459, Section 2.1, page 3.
The paper defines R of N as the sum of mu squared of N minus p times log p,
over primes p at most N, and states that R is positive exactly when a
representation exists. This finite criterion holds for every natural N.
It is independent of the later analytic estimates.
-/

noncomputable section
namespace LeanLab.AlmostPrimes.DudekWeighted

open Finset Real

/-- The paper's R, with the integer Mobius square cast to the reals. -/
def weightedCount (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    ((ArithmeticFunction.moebius (N - p) ^ 2 : ℤ) : ℝ) * log p

/-- The primes with a square-free remainder. A zero remainder is excluded by Squarefree. -/
def goodPrimes (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun p => p.Prime ∧ Squarefree (N - p))

/-- Mobius squared turns the weighted sum into an indicator sum. -/
theorem weightedCount_eq_indicator (N : ℕ) :
    weightedCount N = ∑ p ∈ goodPrimes N, log p := by
  unfold weightedCount goodPrimes
  simp only [sum_filter, ArithmeticFunction.moebius_sq]
  apply sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> by_cases hs : Squarefree (N - p) <;> simp [hprime, hs]

/-- The weighted count is nonnegative. -/
theorem weightedCount_nonneg (N : ℕ) : 0 ≤ weightedCount N := by
  rw [weightedCount_eq_indicator]
  exact sum_nonneg fun p _ => log_natCast_nonneg p

/-- Positive weighted count is equivalent to a prime with positive square-free remainder. -/
theorem weightedCount_pos_iff (N : ℕ) :
    0 < weightedCount N ↔ ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) := by
  rw [weightedCount_eq_indicator,
    sum_pos_iff_of_nonneg (fun p _ => log_natCast_nonneg p)]
  constructor
  · rintro ⟨p, hp, hlog⟩
    simp only [goodPrimes, mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hprime, hs⟩ := hp
    have hlt : p < N := by
      by_contra h
      have heq : p = N := by omega
      subst p
      simp at hs
    exact ⟨p, hprime, hlt, hs⟩
  · rintro ⟨p, hprime, hpN, hs⟩
    refine ⟨p, ?_, log_pos (by exact_mod_cast hprime.one_lt)⟩
    simp only [goodPrimes, mem_filter, mem_Icc]
    exact ⟨⟨hprime.one_lt.le, hpN.le⟩, hprime, hs⟩

/-- The representation criterion in the exact positive summand form of Theorem 1. -/
theorem weightedCount_pos_iff_representation (N : ℕ) :
    0 < weightedCount N ↔
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  rw [weightedCount_pos_iff]
  constructor
  · rintro ⟨p, hp, hpN, hs⟩
    exact ⟨p, N - p, hp, by omega, hs, by omega⟩
  · rintro ⟨p, m, hp, hm, hs, hN⟩
    refine ⟨p, hp, by omega, ?_⟩
    have heq : N - p = m := by omega
    simpa only [heq] using hs

/-- A concrete positive instance: R of three is log two. -/
theorem weightedCount_three : weightedCount 3 = log 2 := by
  rw [weightedCount_eq_indicator]
  have hg : goodPrimes 3 = ({2} : Finset ℕ) := by
    ext p
    simp only [goodPrimes, mem_filter, mem_Icc, mem_singleton]
    constructor
    · rintro ⟨⟨h1, h3⟩, hp, hs⟩
      interval_cases p <;> norm_num at *
    · rintro rfl
      norm_num
  rw [hg, sum_singleton]
  norm_num

end LeanLab.AlmostPrimes.DudekWeighted

#print axioms LeanLab.AlmostPrimes.DudekWeighted.weightedCount_eq_indicator
#print axioms LeanLab.AlmostPrimes.DudekWeighted.weightedCount_nonneg
#print axioms LeanLab.AlmostPrimes.DudekWeighted.weightedCount_pos_iff
#print axioms LeanLab.AlmostPrimes.DudekWeighted.weightedCount_pos_iff_representation
#print axioms LeanLab.AlmostPrimes.DudekWeighted.weightedCount_three
