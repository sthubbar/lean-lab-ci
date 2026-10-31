/-
Kernel Goldbach window 10: every even n in [18820002, 20800000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_10 : wem 18818902 18820002 20800000 &&& gm (wpm 18818902 1981098) (P10k.take 183) =
    wem 18818902 18820002 20800000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
