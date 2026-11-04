import LeanLab.DtRS1998.Task295Sec41Count

/-!
# DtRS1998, Novelty1615: the index 413 of Section 4.1

AI wrote this Lean code. Goldbach is open. Tag: IMPROVEMENT only, a kernel check of a printed number.
Nothing here is ORIGINAL. `Sec41.sec41` proves the two ends prime and that no prime before q413
works, but says nothing on how many primes lie between. This file names that remaining count.
-/

namespace LeanLab.DtRS1998.Novelty1615

/-- The primes of the interval from q1 to q413 of Section 4.1. -/
def sec41Primes : Finset ℕ :=
  (Finset.Icc 33835999990007 33836000002499).filter Nat.Prime

/-- **CITED target.** Twin: the primes from q1 = 33835999990007 to q413 = 33836000002499 number
exactly 413. Source: Deshouillers, te Riele, Saouter 1998, published p. 210, papers/P0037.txt lines
294 to 297, which prints the index 413. Unit U-1615 recomputed the count 413 with a segmented sieve,
scripts/dtrs_sec41.py. A proof needs one primality certificate per prime, as `Sec41.pratt`, and one
factor per composite: over 30 minutes here, so it stays a named sorry. -/
theorem sec41_prime_count : sec41Primes.card = 413 := by
  simpa only [sec41Primes, Task71.primesIn] using Task295.Sec41Count.count_413

/-- Vacuity instance: the interval is nonempty, its two ends are distinct. -/
theorem sec41_interval_vacuity :
    (33835999990007 : ℕ) ∈ Finset.Icc 33835999990007 33836000002499 ∧
      (33836000002499 : ℕ) ∈ Finset.Icc 33835999990007 33836000002499 := by
  simp

end LeanLab.DtRS1998.Novelty1615
