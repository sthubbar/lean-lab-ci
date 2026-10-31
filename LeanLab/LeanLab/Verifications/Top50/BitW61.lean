/-
Kernel Goldbach window 61: every even n in [119800002, 121780000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_61 : wem 119798190 119800002 121780000 &&& gm (wpm2 119798190 1981810) (P10k.take 280) =
    wem 119798190 119800002 121780000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
