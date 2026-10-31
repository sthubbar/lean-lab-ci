/-
Kernel Goldbach window 13: every even n in [24760002, 26740000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_13 : wem 24758902 24760002 26740000 &&& gm (wpm 24758902 1981098) (P10k.take 183) =
    wem 24758902 24760002 26740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
