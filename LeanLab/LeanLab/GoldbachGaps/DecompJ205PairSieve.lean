import LeanLab.GoldbachGaps.Goldston1990Main

/-!
P0030 Goldston 1990 page 287 displays 11, 13 and 14.
This is the isolated prime difference sieve input for the DecompJ205 route.
The Euler product omits the fixed twin prime constant, which the absolute bound absorbs.
This leaf is open. It is a cited analytic input.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.GoldbachGaps.DecompJ205
open Real Finset

/-- LEAF P0030 page 287 displays 11, 13 and 14. The weighted count of prime pairs
with positive even difference k and both primes at most N is at most an absolute
constant times N and the singular Euler product. The absolute constant absorbs
2 times the twin prime constant and the finitely many small N cases. -/
theorem leaf_pair_sieve_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ N k : ℕ, 3 ≤ N → 0 < k → Even k → k ≤ N →
      (∑ p ∈ Icc 1 (N - k), if p.Prime ∧ (p + k).Prime then
        Real.log (p : ℝ) * Real.log ((p + k : ℕ) : ℝ) else 0) ≤
      C * (∏ q ∈ k.primeFactors.filter (fun q => 2 < q),
        ((q : ℝ) - 1) / ((q : ℝ) - 2)) * N := by
  sorry

end LeanLab.GoldbachGaps.DecompJ205
