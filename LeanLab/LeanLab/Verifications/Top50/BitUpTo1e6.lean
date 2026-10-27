/-
EvenGoldbachUpTo 1000000 by one bignum equality, the sieve of BitSieve.lean.
Every even n with 4 ≤ n ≤ 10^6 is p + q with q among the first 99 primes, at most 523.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem check_1e6 : em 4 1000000 &&& gm (pm 1000001) (P10k.take 99) = em 4 1000000 := by
  decide +kernel

theorem evenGoldbachUpTo_1e6 : EvenGoldbachUpTo 1000000 :=
  upTo_of_check (by norm_num) (take_prime 99) check_1e6

end LeanLab.Verifications.Top50.Bits
