/-
P0006, page 2, bounded search and its constant number of Jacobi tests.
The count is the number of primes through the first witness, or through B when
there is no witness. It does not count primality testing or Jacobi arithmetic.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.Algorithm98

open scoped Asymptotics

namespace LeanLab.HelfgottPlatt.Task98

/-- Page 2, steps 3 to 5. Count prime candidates through the selected witness,
or all primes at most B when no witness exists. -/
def witnessChecks (N B : ℕ) : ℕ :=
  match firstWitness N B with
  | none => ((Finset.range (B + 1)).filter Nat.Prime).card
  | some a => ((Finset.range (a + 1)).filter Nat.Prime).card

/-- Page 2, the bounded search makes no more Jacobi tests than there are
primes at most B. -/
theorem witnessChecks_le (N B : ℕ) :
    witnessChecks N B ≤ ((Finset.range (B + 1)).filter Nat.Prime).card := by
  cases hw : firstWitness N B with
  | none => simp [witnessChecks, hw]
  | some a =>
    simp only [witnessChecks, hw]
    have haB := (firstWitness_eq_some.mp hw).2.1
    exact Finset.card_le_card (Finset.filter_subset_filter Nat.Prime
      (Finset.range_mono (Nat.add_le_add_right haB 1)))

/-- Page 3, B = 29 gives at most ten Jacobi tests for every candidate N. -/
theorem witnessChecks_29 (N : ℕ) : witnessChecks N 29 ≤ 10 := by
  calc
    witnessChecks N 29 ≤ ((Finset.range (29 + 1)).filter Nat.Prime).card :=
      witnessChecks_le N 29
    _ = 10 := U1511.card_primes_le_29

/-- Page 2, for fixed B the number of Jacobi tests is O of 1 as N grows.
This counts calls and does not assert the arithmetic complexity of a call. -/
theorem witnessChecks_isBigO (B : ℕ) :
    (fun N : ℕ => (witnessChecks N B : ℝ))
      =O[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound
    (((Finset.range (B + 1)).filter Nat.Prime).card : ℝ)
  apply Filter.Eventually.of_forall
  intro N
  have hc : (witnessChecks N B : ℝ) ≤
      (((Finset.range (B + 1)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast witnessChecks_le N B
  have hn : (0 : ℝ) ≤ (witnessChecks N B : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn, abs_one, mul_one] using hc

/-- Pages 2 and 3, vacuity instances for successful and exhausted searches. -/
theorem witnessCost_instances :
    witnessChecks 13 2 = 1 ∧ witnessChecks 17 2 = 1 ∧
      witnessChecks 17 3 = 2 ∧ witnessChecks 17 29 = 2 := by
  decide +kernel

end LeanLab.HelfgottPlatt.Task98
