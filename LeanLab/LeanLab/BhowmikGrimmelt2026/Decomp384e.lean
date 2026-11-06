/-
The unweighted ordered prime count defined on P0029 page 2.
The logarithmic comparisons justify its relation to the weighted prime count on page 4.
No unweighted Hardy Littlewood asymptotic is asserted.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp384b

namespace LeanLab.BhowmikGrimmelt2026

/-- The ordered prime pair count r2 prime from P0029 page 2. -/
def primeCount384 (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)).card

/-- Positivity of the paper's prime count is exactly prime pair representability.
Source: P0029 page 2, the sentence following the definition. -/
theorem primeCount_pos_iff384 (N : ℕ) : 0 < primeCount384 N ↔ IsGoldbachSum N := by
  rw [primeCount384, Finset.card_pos]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨hpN, hprime, hother⟩ := Finset.mem_filter.mp hp
    exact ⟨p, N - p, hprime, hother, Nat.add_sub_of_le (by simpa using hpN)⟩
  · rintro ⟨p, q, hp, hq, heq⟩
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, ?_⟩⟩
    simpa only [show N - p = q by omega] using hq

/-- Zero prime count is exactly failure of prime pair representability.
Source: P0029 pages 1 and 2, the exceptional set definition and the prime count. -/
theorem primeCount_zero_iff384 (N : ℕ) : primeCount384 N = 0 ↔ ¬ IsGoldbachSum N := by
  simpa only [not_lt, Nat.le_zero] using (primeCount_pos_iff384 N).not

/-- The logarithmic prime count is the sum of the logarithm products over the prime pairs.
Source: P0029 page 4, the replacement of the prime indicator by its logarithmic weight. -/
theorem primeR2_eq_sum_primes384 (N : ℕ) :
    primeR2_384 N = ∑ k ∈ (Finset.range (N + 1)).filter
      (fun k => k.Prime ∧ (N - k).Prime), Real.log k * Real.log (N - k : ℕ) := by
  rw [primeR2_384, Finset.sum_filter]

/-- The weighted prime count lies between log two squared and log N squared times the count.
Source: derived finite comparisons for P0029 pages 2 and 4.
These inequalities assert no asymptotic equivalence. -/
theorem primeR2_count_bounds384 (N : ℕ) (hN : 1 ≤ N) :
    (Real.log 2) ^ 2 * (primeCount384 N : ℝ) ≤ primeR2_384 N ∧
      primeR2_384 N ≤ (Real.log N) ^ 2 * (primeCount384 N : ℝ) := by
  rw [primeR2_eq_sum_primes384]
  let S := (Finset.range (N + 1)).filter (fun k => k.Prime ∧ (N - k).Prime)
  have hlo (k : ℕ) (hk : k ∈ S) :
      (Real.log 2) ^ 2 ≤ Real.log k * Real.log (N - k : ℕ) := by
    obtain ⟨hkN, hp, hq⟩ := Finset.mem_filter.mp hk
    have hpk : Real.log (2 : ℝ) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    have hqk : Real.log (2 : ℝ) ≤ Real.log (N - k : ℕ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq.two_le)
    rw [pow_two]
    exact mul_le_mul hpk hqk (Real.log_nonneg (by norm_num))
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
  have hhi (k : ℕ) (hk : k ∈ S) :
      Real.log k * Real.log (N - k : ℕ) ≤ (Real.log N) ^ 2 := by
    obtain ⟨hkN, hp, hq⟩ := Finset.mem_filter.mp hk
    have hpk : Real.log (k : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hp.pos)
        (by exact_mod_cast (show k ≤ N by simpa using hkN))
    have hqk : Real.log (N - k : ℕ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast Nat.sub_le N k)
    rw [pow_two]
    exact mul_le_mul hpk hqk (Real.log_nonneg (by exact_mod_cast hq.one_lt.le))
      (Real.log_nonneg (by exact_mod_cast hN))
  constructor
  · have h := Finset.sum_le_sum hlo
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm, primeCount384] using h
  · have h := Finset.sum_le_sum hhi
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm, primeCount384] using h

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.primeCount384
#print axioms LeanLab.BhowmikGrimmelt2026.primeCount_pos_iff384
#print axioms LeanLab.BhowmikGrimmelt2026.primeCount_zero_iff384
#print axioms LeanLab.BhowmikGrimmelt2026.primeR2_eq_sum_primes384
#print axioms LeanLab.BhowmikGrimmelt2026.primeR2_count_bounds384
