/-
P0059 Corollary 1.2, arXiv 1407.7902v1 page 2 and proof on page 13.
CONDITIONAL ON the cited Theorem 1.1 rows and the even verification.
AI wrote this Lean code. CODEX task64 replaced the standalone sorry by
its existing conditional derivation on 2026-10-25.
-/
import LeanLab.KadiriLumley2014.Corollary
import LeanLab.KadiriLumley2014.RowInputs

namespace LeanLab.KadiriLumley2014

/-- Corollary 1.2: every odd number larger than 5 and smaller than
`1 966 196 911 × 4 · 10^18 = 7.864… · 10^27` is the sum of at most three primes. For odd
`n ≥ 7` the lab states exactly three, which is what the proof gives. -/
theorem corollary1_2 : ∀ n : ℕ, Odd n → 5 < n → n < 1966196911 * (4 * 10 ^ 18) →
    IsTernarySum n :=
  corollary1_2_of row_4e18 row_60 LeanLab.Verifications.oesilva_even

end LeanLab.KadiriLumley2014
