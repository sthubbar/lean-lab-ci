/-
Kernel Goldbach window 30: every even n in [58420002, 60400000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_30 : wem 58418902 58420002 60400000 &&& gm (wpm 58418902 1981098) (P10k.take 183) =
    wem 58418902 58420002 60400000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
